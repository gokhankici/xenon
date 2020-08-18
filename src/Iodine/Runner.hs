{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

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
  , computeFInfo
  ) where

import           Iodine.IodineArgs
import           Iodine.Analyze.CounterExample (generateCounterExampleGraphs)
import           Iodine.Language.Annotation
import           Iodine.Language.IR (prettyShow, Module(..))
import           Iodine.Language.IRParser
import           Iodine.Language.PrologParser
import           Iodine.Pipeline
import           Iodine.Transform.Fixpoint.Common
import           Iodine.Transform.Horn
import           Iodine.Types
import           Iodine.Analyze.ModuleSummary (SummaryMap)
import           Iodine.Utils

import           Control.Carrier.Error.Either
import           Control.Carrier.Trace.Print
import           Control.Carrier.Writer.Strict
import qualified Control.Exception as E
import           Control.Lens hiding ((<.>))
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Char
import qualified Data.ByteString.Lazy as B
import           Data.Foldable
import qualified Data.IntMap.Strict as IM
import qualified Data.HashMap.Strict as HM
import qualified Data.IntSet as IS
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Language.Fixpoint.Misc as FM
import qualified Language.Fixpoint.Solver as F
import qualified Language.Fixpoint.Types as FT
import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Fixpoint.Types.Constraints as FCons
import qualified Language.Fixpoint.Solver.Monad as FSM
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process
import           Text.PrettyPrint.HughesPJ (render)
import           Text.Printf
import           Data.List (intersperse, foldl1')
import qualified Data.HashSet as HS
import qualified Data.Sequence as SQ

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
verilogToIR :: FilePath -> FilePath -> String -> [String] -> IO FilePath
-- -----------------------------------------------------------------------------
verilogToIR iverilogDir verilogFile topModule includeDirs = do
  runPreProcessor
  runIVL
  return irFile
  where
    -- run ivlpp preprocessor on the given verilog file
    runPreProcessor = withCurrentDirectory verilogDir $ do
      let preprocessor = iverilogDir </> "ivlpp" </> "ivlpp"
      args <-
        case includeDirs of
          [] -> return [verilogFile]
          _  -> createIncludesFile >> return ["-F", includesFile, verilogFile]
      (rc, out, err) <- readProcessWithExitCode preprocessor args ""
      case rc of
        ExitSuccess ->
          writeFile preprocFile out
        ExitFailure _ -> do
          putStrLn $ cmdStr (preprocessor : args)
          hPutStrLn stderr "Preprocessing of the following file failed:"
          hPutStrLn stderr verilogFile
          hPutStrLn stderr err
          exitFailure

    includesFile = verilogFile <.> "includes"

    createIncludesFile =
      withFile includesFile WriteMode $ \h ->
        for_ includeDirs $ \i -> do
          hPutStr   h "I:"
          if i !! 0 == '/'
            then hPutStrLn h i
            else canonicalizePath (replaceFileName verilogFile i)
                 >>= hPutStrLn h

    cmdStr = foldl1' (++) . intersperse " "

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
          putStrLn $ cmdStr $ ivl : ivlArgs
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
  let topModule = T.unpack $ view afTopModule af
      includeDirs = T.unpack <$> (view afIncludeDirs af)
  irFile <- verilogToIR iverilogDir fileName topModule includeDirs
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
        & handleTrace ia
        & handleMonads ia
      case mNormalizedOutput of
        Right (_, (normalizedIR, _)) -> do traverse_ (putStrLn . toStr) normalizedIR
                                           putStrLn sep
                                        where toStr a = prettyShow a ++ "\n"
                                              sep = replicate 80 '-'
        Left e      -> errorHandle e
      return True
  | onlyVCGen = do computeFInfo ia af >>= FCons.saveQuery config . fst
                   return True
  | otherwise = do
      (finfo, (threadTypes, af', moduleMap, summaryMap)) <- computeFInfo ia af
      result <- F.solve config finfo
      let stat = FT.resStatus result
          statStr = render . FT.resultDoc
      FM.colorStrLn (FT.colorResult stat) (statStr stat)
      let safe = FT.isSafe result
      printFailedConstraints finfo stat
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
      printResultAnalysis af' moduleMap summaryMap finfo threadTypes result
      unless (safe || benchmarkMode) $
        generateCounterExampleGraphs af' moduleMap summaryMap finfo abduction
      when printSolution $
        (readFile fqoutFile >>= traverse_ putStrLn . take 300 . lines)
        `E.catch` (\(_ :: E.IOException) -> return ())
      return safe
  where
    config :: FC.Config
    config = FC.defConfig { FC.eliminate = FC.Some
                          , FC.save      = not noSave
                          , FC.srcFile   = fileName
                          , FC.metadata  = True
                          , FC.minimize  = delta
                          , FC.solverTrace = True
                          }

    fqoutFile :: FilePath
    fqoutFile =
      let (dir, base) = splitFileName fileName
      in dir </> ".liquid" </> (base <.> "fqout")

printResultAnalysis :: AnnotationFile
                    -> HM.HashMap Id (Module Int)
                    -> SummaryMap
                    -> FInfo
                    -> IM.IntMap ThreadType
                    -> FT.Result (Integer, HornClauseId)
                    -> IO ()
printResultAnalysis af moduleMap summaryMap finfo threadTypes = \case
  FT.Result FT.Safe _ _        -> return ()
  FT.Result (FT.Crash _ _) _ _ -> return ()
  FT.Result (FT.Unsafe ids) sol _ -> do
    let invNo = case nub' id $ (hcStmtId . snd) <$> ids of
                  [n] -> n
                  ns  -> error $ show ns
        invExpr = sol HM.! (FT.KV $ FT.symbol $ "inv" <> show invNo)
        qualifs = FSM.toTracePred invExpr
        go acc = \case
          FSM.TraceConstantTime (FSM.TraceVar _ v _) ->
            acc & _1 %~ HS.insert v
          FSM.TracePublic (FSM.TraceVar _ v _) ->
            acc & _2 %~ HS.insert v
          _ -> acc
        (ctVars, pubVars) = foldl' go (mempty, mempty) qualifs
        noVars = SQ.length $ variables m
    printf "# variables    : %3d\n" noVars
    printf "# non-ct  vars : %3d\n" (noVars - HS.size ctVars)
    printf "# non-pub vars : %3d\n" (noVars - HS.size pubVars)
    where
      topModuleName = af ^. afTopModule
      m = moduleMap HM.! topModuleName

-- | given file name should be and IR file
computeFInfo :: IodineArgs -> AnnotationFile -> IO PipelineOutput
computeFInfo ia@IodineArgs{..} af = do
  irFileContents <- readIRFile ia fileName
  let irReader = parse (fileName, irFileContents)
  mFInfo <- pipeline af irReader ia
            & handleTrace ia
            & handleMonads ia
  case mFInfo of
    Right res -> return res
    Left e    -> errorHandle e

handleMonads :: IodineArgs
             -> ErrorC IodineException (WriterC Output IO) a
             -> IO (Either IodineException a)
handleMonads ia act = handleOutput ia $ runError act

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

printFailedConstraints :: FInfo -> FT.FixResult (FT.SubcId, HornClauseId) -> IO ()
printFailedConstraints finfo stat@(FT.Unsafe failedConstraints) =
  for_ (fst <$> failedConstraints) $ \constraintId -> do
    let constraint = FT.cm finfo HM.! constraintId
        rhs = FT.srhs constraint
        expr = FT.reftPred $ FT.sr_reft rhs
    case expr of
      FT.PIff (FT.EVar s) (FT.EVar _) -> do
        let t = FT.symbolSafeText s
            t1 = T.drop 3 t -- no prefix TL_
            t2 = T.dropWhileEnd isDigit t1 -- no tread number at end
            t3 = T.dropEnd 2 t2 -- drop _T
        FM.colorStrLn
          (FT.colorResult stat)
          ("FAILED " <> T.unpack t3 <> " :: " <> FT.showFix expr)
      _ -> FM.colorStrLn (FT.colorResult stat) ("FAILED " <> FT.showFix expr)
printFailedConstraints _ _ = return ()

-- -----------------------------------------------------------------------------
-- Common Functions
-- -----------------------------------------------------------------------------

errorHandle :: IodineException -> IO a
errorHandle = E.throwIO
