{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Runner
  ( generateIR
  , run
  , main
  , readIRFile
  ) where

import           Iodine.IodineArgs
import           Iodine.Language.Annotation
import           Iodine.Language.IRParser
import           Iodine.Language.PrologParser
import           Iodine.Pipeline
import           Iodine.Transform.Fixpoint.Common
import           Iodine.Transform.Horn
import           Iodine.Types

import qualified Control.Exception as E
import           Control.Lens (view)
import           Control.Monad
import qualified Data.ByteString.Lazy as B
import           Data.Foldable
import           Data.Function
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Language.Fixpoint.Misc as FM
import qualified Language.Fixpoint.Solver as F
import qualified Language.Fixpoint.Types as FT
import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Fixpoint.Types.Constraints as FCons
import           Polysemy hiding (run)
import           Polysemy.Error
import           Polysemy.Output
import           Polysemy.Trace
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process
import           Text.PrettyPrint.HughesPJ (render)
import           Text.Printf


-- -----------------------------------------------------------------------------
main :: IO ()
-- -----------------------------------------------------------------------------
-- | Parses the command line arguments automatically, and runs the tool.
-- If the program is not constant time, the process exists with a non-zero return code.
main = do
  safe <- getArgs >>= parseArgsWithError >>= run
  unless safe exitFailure

-- -----------------------------------------------------------------------------
run :: IodineArgs -> IO Bool
-- -----------------------------------------------------------------------------
-- | Runs the verification process, and returns 'True' if the program is constant time.
run a = generateIR a >>= checkIR

-- -----------------------------------------------------------------------------
generateIR :: IodineArgs -> IO (IodineArgs, AnnotationFile)
-- -----------------------------------------------------------------------------
generateIR IodineArgs{..} = do
  runPreProcessor
  af <- parseAnnotations <$> B.readFile annotFile
  let topModule =  T.unpack $ view afTopModule af
  let result = IodineArgs { fileName   = irFile
                          , moduleName = topModule
                          , ..
                          }
  runIVL topModule
  return (result, af)


  where
    -- run ivlpp preprocessor on the given verilog file
    runPreProcessor = withCurrentDirectory verilogDir $ do
      let preprocessor = iverilogDir </> "ivlpp" </> "ivlpp"
      (rc, out, err) <- readProcessWithExitCode preprocessor [verilogFile] ""
      case rc of
        ExitSuccess ->
          writeFile preprocFile out
        ExitFailure _ -> do
          hPutStrLn stderr "Preprocessing of the following file failed:"
          hPutStrLn stderr verilogFile
          hPutStrLn stderr err
          exitFailure

    -- compile the Verilog file into IR
    runIVL topModule = do
      let ivl     = iverilogDir </> "ivl"
          ivlArgs = [ "-M", topModule
                    , "-O", irFile
                    , preprocFile
                    ]
      (rc, _out, err) <- readProcessWithExitCode ivl ivlArgs ""
      case rc of
        ExitSuccess -> return ()
        ExitFailure _ -> do
          printMsg "Generating IR from the following Verilog file failed:" err
          exitFailure

    printMsg msg err =
      forM_ (msg:[verilogFile, preprocFile, err]) (hPutStrLn stderr)

    verilogFile = fileName
    verilogDir  = takeDirectory verilogFile
    filePrefix  = verilogDir </> "" <.> dropExtensions (takeFileName verilogFile)
    preprocFile = filePrefix <.> "preproc" <.> "v"
    irFile      = filePrefix <.> "pl"


-- -----------------------------------------------------------------------------
checkIR :: (IodineArgs, AnnotationFile) -> IO Bool
-- -----------------------------------------------------------------------------
checkIR (ia@IodineArgs{..}, af)
  | printIR = do
      irFileContents <- readIRFile ia fileName
      mNormalizedOutput <-
        normalizeIR af (parse (fileName, irFileContents)) ia
        & handleMonads ia
      case mNormalizedOutput of
        Right (_, (normalizedIR, _)) -> printList normalizedIR
        Left e      -> errorHandle e
      return True
  | onlyVCGen = do computeFInfo >>= FCons.saveQuery config . fst
                   return True
  | otherwise = do
      (finfo, threadTypes) <- computeFInfo
      result <- F.solve config finfo
      let stat = FT.resStatus result
          statStr = render . FT.resultDoc
      FM.colorStrLn (FT.colorResult stat) (statStr stat)
      let safe = FT.isSafe result
      unless (noFPOutput || delta) $
        (readFile fqoutFile >>= putStrLn) `E.catch` (\(_ :: E.IOException) -> return ())
      when delta $ do
        let mds = case stat of
                    FT.Unsafe cs -> snd <$> cs
                    _ -> error "unreachable"
            tids =
              foldMap
              (\HornClauseId{..} ->
                 case hcType of
                   Interference l -> IS.insert hcStmtId $ IS.fromList l
                   _ -> IS.singleton hcStmtId)
              mds
        for_ (IS.toList tids) $ \tid ->
          printf "Thread #%d: %s\n" tid (show $ threadTypes IM.! tid)
      return safe
  where
    computeFInfo = do
      print verbosity
      irFileContents <- readIRFile ia fileName
      let irReader = parse (fileName, irFileContents)
      mFInfo <- pipeline af irReader ia & handleMonads ia
      case mFInfo of
        Right finfo -> return finfo
        Left e      -> errorHandle e

    config :: FC.Config
    config = FC.defConfig { FC.eliminate = FC.Some
                          , FC.save      = not noSave
                          , FC.srcFile   = fileName
                          , FC.metadata  = True
                          , FC.minimize  = delta
                          }

    fqoutFile :: FilePath
    fqoutFile =
      let (dir, base) = splitFileName fileName
      in dir </> ".liquid" </> (base <.> "fqout")

handleMonads :: IodineArgs
             -> Sem '[Error IodineException, Trace, Output String, Embed IO, Final IO] a
             -> IO (Either IodineException a)
handleMonads IodineArgs{..} act =
  act
  & errorToIOFinal
  & handleTrace
  & handleOutput
  & embedToFinal
  & runFinal
  where
    handleTrace :: Member (Embed IO) r => Sem (Trace ': r) a -> Sem r a
    handleTrace =
      if verbosity /= Loud || benchmarkMode
      then ignoreTrace
      else traceToIO

    handleOutput :: Member (Embed IO) r => Sem (Output String ': r) a -> Sem r a
    handleOutput =
      if verbosity == Quiet || benchmarkMode
      then ignoreOutput
      else runOutputSem (embed . hPutStrLn stderr)

printList :: Show a => L a -> IO ()
printList l = do
  traverse_ (putStrLn . toStr) l
  putStrLn  sep
  where
    toStr a = show a ++ "\n"
    sep = replicate 80 '-'


readIRFile :: IodineArgs -> String -> IO String
readIRFile ia fileName =
  if prettyProlog ia
  then do fileContents <- TIO.readFile fileName
          return $ case parseProlog fileName fileContents of
                     Right ms -> unlines $ show <$> ms
                     Left msg -> error msg
  else readFile fileName

-- -----------------------------------------------------------------------------
-- Common Functions
-- -----------------------------------------------------------------------------

errorHandle :: IodineException -> IO a
errorHandle = E.throwIO
