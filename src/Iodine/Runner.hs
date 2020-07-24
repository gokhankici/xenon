{-# OPTIONS_GHC -Wno-missing-signatures #-}

{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Runner
  ( generateIR
  , runner
  , main
  , readIRFile
  , verilogToIR
  ) where

import           Iodine.IodineArgs
import           Iodine.Analyze.CounterExample (generateCounterExampleGraphs)
import           Iodine.Language.Annotation
import           Iodine.Language.IR (prettyShow)
import           Iodine.Language.IRParser
import           Iodine.Language.PrologParser
import           Iodine.Pipeline
import           Iodine.Transform.Fixpoint.Common
import           Iodine.Transform.Horn
import           Iodine.Types

import           Control.Carrier.Error.Either
import           Control.Carrier.Trace.Print
import           Control.Carrier.Writer.Strict
import qualified Control.Exception as E
import           Control.Lens (view)
import           Control.Monad
import           Control.Monad.IO.Class
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
  safe <- getArgs >>= parseArgsWithError >>= runner
  unless safe exitFailure

-- -----------------------------------------------------------------------------
runner :: IodineArgs -> IO Bool
-- -----------------------------------------------------------------------------
-- | Runs the verification process, and returns 'True' if the program is constant time.
runner a = generateIR a >>= checkIR

-- -----------------------------------------------------------------------------
verilogToIR :: FilePath -> FilePath -> String -> IO FilePath
-- -----------------------------------------------------------------------------
verilogToIR iverilogDir verilogFile topModule = do
  runPreProcessor
  runIVL
  return irFile
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
    runIVL = do
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

    verilogDir  = takeDirectory verilogFile
    filePrefix  = verilogDir </> "" <.> dropExtensions (takeFileName verilogFile)
    preprocFile = filePrefix <.> "preproc" <.> "v"
    irFile      = filePrefix <.> "pl"

-- -----------------------------------------------------------------------------
generateIR :: IodineArgs -> IO (IodineArgs, AnnotationFile)
-- -----------------------------------------------------------------------------
generateIR IodineArgs{..} = do
  af <- parseAnnotations <$> B.readFile annotFile
  let topModule =  T.unpack $ view afTopModule af
  irFile <- verilogToIR iverilogDir fileName topModule
  let result = IodineArgs { fileName   = irFile
                          , moduleName = topModule
                          , ..
                          }
  return (result, af)

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
        Right (_, (normalizedIR, _)) -> do traverse_ (putStrLn . toStr) normalizedIR
                                           putStrLn sep
                                        where toStr a = prettyShow a ++ "\n"
                                              sep = replicate 80 '-'
        Left e      -> errorHandle e
      return True
  | onlyVCGen = do computeFInfo >>= FCons.saveQuery config . fst
                   return True
  | otherwise = do
      (finfo, (threadTypes, af', moduleMap, summaryMap)) <- computeFInfo
      result <- F.solve config finfo
      let stat = FT.resStatus result
          statStr = render . FT.resultDoc
      FM.colorStrLn (FT.colorResult stat) (statStr stat)
      let safe = FT.isSafe result
      -- unless (safe || noFPOutput || delta) $
      --   (readFile fqoutFile >>= traverse_ putStrLn . take 300 . lines)
      --   `E.catch` (\(_ :: E.IOException) -> return ())
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
      unless (safe || benchmarkMode) $
        generateCounterExampleGraphs af' moduleMap summaryMap finfo
      return safe
  where
    computeFInfo = do
      print verbosity
      irFileContents <- readIRFile ia fileName
      let irReader = parse (fileName, irFileContents)
      mFInfo <- pipeline af irReader ia
                & handleTrace ia
                & handleMonads ia
      case mFInfo of
        Right res -> return res
        Left e    -> errorHandle e

    config :: FC.Config
    config = FC.defConfig { FC.eliminate = FC.Some
                          , FC.save      = not noSave
                          , FC.srcFile   = fileName
                          , FC.metadata  = True
                          , FC.minimize  = delta
                          , FC.solverTrace = True
                          }

    -- fqoutFile :: FilePath
    -- fqoutFile =
    --   let (dir, base) = splitFileName fileName
    --   in dir </> ".liquid" </> (base <.> "fqout")

handleMonads :: IodineArgs
             -> WriterC Output (ErrorC IodineException IO) a
             -> IO (Either IodineException a)
handleMonads ia act = runError $ handleOutput ia act

handleTrace :: IodineArgs -> TraceC m a -> m a
handleTrace IodineArgs{..} =
  if verbosity /= Loud || benchmarkMode
  then runTraceIgnore
  else runTracePrint

handleOutput :: MonadIO m => IodineArgs -> WriterC Output m a -> m a
handleOutput IodineArgs{..} act =
  if verbosity == Quiet || benchmarkMode
  then snd <$> runWriter act
  else do (logs, result) <- runWriter act
          liftIO (traverse_ (hPutStrLn stderr) logs)
          return result

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
