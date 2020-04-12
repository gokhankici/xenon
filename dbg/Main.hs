{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE GADTs #-}

module Main where

import           Iodine.Analyze.FQOutAnalysis
import           Iodine.Analyze.ModuleSummary
import           Iodine.IodineArgs
import qualified Iodine.IodineArgs as IA
import           Iodine.Language.Annotation
import           Iodine.Language.IR as IR
import           Iodine.Language.IRParser
import           Iodine.Pipeline (normalizeIR)
import           Iodine.Runner (generateIR, readIRFile)
import           Iodine.Transform.Fixpoint.Query
import           Iodine.Transform.Merge
import           Iodine.Transform.Normalize
import           Iodine.Transform.VCGen
import           Iodine.Transform.VariableRename
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.Error.Either
import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Carrier.Trace.Print (Trace)
import qualified Control.Carrier.Trace.Print as PT
import           Control.Carrier.Writer.Strict
import qualified Control.Exception as E
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Bifunctor
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Hashable
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import           Data.Maybe
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import qualified Language.Fixpoint.Misc as FM
import qualified Language.Fixpoint.Solver as F
import qualified Language.Fixpoint.Types as FT
import qualified Language.Fixpoint.Types.Config as FC
import           System.Directory
import           System.Environment
import           System.FilePath.Posix
import           System.IO
import           System.IO.Error
import           Text.PrettyPrint.HughesPJ (render)
import           Text.Printf

-- #############################################################################
-- Debug Configuration
-- #############################################################################
-- | iodine arguments
iodineVerbosity = Loud
disableFQSave = False

-- debugVerilogFile = "benchmarks" </> "yarvi" </> "shared" </> "test-01.v"
-- debugAnnotationFile = defaultAnnotFile debugVerilogFile
debugVerilogFile = "benchmarks" </> "yarvi" </> "shared" </> "yarvi.v"
debugAnnotationFile = "benchmarks" </> "yarvi" </> "shared" </> "annot-yarvi_fixed.json"

-- | this is the code that runs after the vcgen step
debug :: D sig m => Debug4 sig m
debug = debug4

-- | takes the iodine args and successful result of the 'debug' as an input
runPipeline :: RunFixpoint
runPipeline = runFixpoint
-- #############################################################################


allRegisterDependencies :: D sig m => Id -> Id -> m Ids
allRegisterDependencies mn var = do
  Module{..} <- asks @ModuleMap (! mn)
  ModuleSummary{..} <- asks (! mn)
  -- trace' "variables" (toList variables)
  let g = variableDependencies
      toId = (variableDependencyNodeMap !)
      toVar = (invVariableDependencyNodeMap IM.!)
      -- varNo = toId var
  -- trace ("pre of " ++ T.unpack var ++ " " ++ show varNo) (first toVar <$> G.lpre g varNo)
  -- trace ("pre of " ++ T.unpack var) (G.lpre g (toId var))
  let isReg r = Register r `elem` variables
      wl regs _ SQ.Empty = return regs
      wl regs history (n SQ.:<| ns) = -- do
        -- trace' "wl" (regs, history, n, ns)
        if IS.member n history
          then wl regs history ns
          else do
          let history' = IS.insert n history
              ps = SQ.filter (not . (`IS.member` history)) $ toSequence $ G.pre g n
              nv = toVar n
              (regs', ns') =
                if isReg nv
                then (HS.insert nv regs, ns)
                else foldl'
                     (\(rs, vns) vn ->
                        let v = toVar vn
                        in if isReg v
                           then (HS.insert v rs, ns)
                           else (rs, vns SQ.|> vn))
                     (regs, ns)
                     ps
          -- trace' "vn" (toVar n)
          -- trace' "ps" (toVar <$> ps)
          -- trace' "ps'" (toVar <$> G.pre g n)
          wl regs' history' ns'
  let varId  = toId var
      preVarIds = toSequence $ G.pre g varId
  wl mempty mempty preVarIds
  -- regDeps <- wl mempty mempty preVarIds
  -- trace
  --   (printf "register dependencies of %s in module %s" var mn)
  --   regDeps
  -- return regDeps

printThreadDeps :: D sig m => m ()
printThreadDeps = do
  ModuleSummary{..} <- asks @SummaryMap (! "mips_pipeline")
  output [printGraph threadDependencies show]

getCondVars as = execState @Ids mempty $ do
  let goStmt = \case
        Block{..} -> traverse_ goStmt blockStmts
        Assignment{..} -> return ()
        IfStmt{..} -> do
          modify (HS.union $ getVariables ifStmtCondition)
          goStmt ifStmtThen
          goStmt ifStmtElse
        Skip{} -> return ()
  traverse_ goStmt (abStmt <$> as)

getMissingInitialEquals Module{..} = do
  PT.trace $ printf "getMissingInitialEquals - %s" moduleName
  allInitEqs :: Ids <- asks (HM.! moduleName)
  let isInitEq = (`elem` allInitEqs)
  registersThatAffectConditions <-
    fold
    <$> (toSequence <$> getCondVars alwaysBlocks
         >>= traverse (allRegisterDependencies moduleName))
  trace "registers that affect conditions" (HS.toList registersThatAffectConditions)
  let missingRegs = HS.filter (not . isInitEq) registersThatAffectConditions
  trace "missing registers" (moduleName, HS.toList missingRegs)
  return missingRegs

debug1 :: D sig m => m ()
debug1 = do
  ModuleSummary{..} <- asks @SummaryMap (! "mux3")
  PT.trace $ show portDependencies
  PT.trace $ show isCombinatorial

debug2 :: D sig m => m ()
debug2 = do
  ir <- ask @IRs
  allIEs <- computeAllInitialEqualVars ir
  traverse_ getMissingInitialEquals ir
    & runReader allIEs

debug3 :: D sig m => m ()
debug3 = do
  ModuleSummary{..} <- asks @SummaryMap (! "yarvi")
  PT.trace $
    printGraph threadDependencies (\n -> "#" <> show n)

type Debug4 sig m = VCGenOutput -> m PipelineData
debug4 :: D sig m => Debug4 sig m
debug4 vcOut = do
  modules <- ask
  finfo <- constructQuery modules vcOut
  (finfo,) <$> ((,,) <$> ask <*> ask <*> ask)

type A = Int
type M = Module A
type IRs = L (Module Int)
type ModuleMap = HM.HashMap Id (Module Int)
type G sig m = ( Has (Error IodineException) sig m
               , Has Trace sig m
               , Has (Writer Output) sig m
               , Effect sig
               )
type D sig m = ( G sig m
               , Has (Reader AnnotationFile) sig m
               , Has (Reader ModuleMap) sig m
               , Has (Reader SummaryMap) sig m
               , Has (Reader IRs) sig m
               )

type IRReaderM = PT.TraceC (WriterC Output (ErrorC IodineException IO))
debugPipeline :: AnnotationFile -> IRReaderM (L (Module ())) -> IodineArgs -> IRReaderM PipelineData
debugPipeline af irReader ia = do
  (af', normalizedOutput@(normalizedIR, _)) <- normalizeIR af irReader ia
  runReader af' $ do
    let normalizedIRMap = mkMap IR.moduleName normalizedIR
    moduleSummaries <- createModuleSummaries normalizedIR normalizedIRMap
    (vcgen normalizedOutput >>= debug)
      & runReader moduleSummaries
      & runReader normalizedIRMap
      & runReader normalizedIR

runDefaultPipeline _ = return ()

type PipelineData  = (FInfo, PipelineData2)
type PipelineData2 = (AnnotationFile, ModuleMap, SummaryMap)
type RunFixpoint  = IodineArgs -> PipelineData -> IO FQOutAnalysisOutput
type DebugOutput  = (PipelineData2, FQOutAnalysisOutput)

runFixpoint :: RunFixpoint
runFixpoint IodineArgs{..} (finfo, (af, mm, sm)) = do
  result <- F.solve config finfo
  let stat = FT.resStatus result
      statStr = render . FT.resultDoc
  FM.colorStrLn (FT.colorResult stat) (statStr stat)
  findFirstNonCTVars result af mm sm
  where
    config = FC.defConfig { FC.eliminate = FC.Some
                          , FC.save      = not noSave
                          , FC.srcFile   = fileName
                          , FC.metadata  = True
                          , FC.minimize  = delta
                          }


runner :: IO DebugOutput
runner = do
  (ia@IodineArgs{..}, af) <- debugArgs >>= generateIR
  irFileContents <- readIRFile ia fileName
  res <- debugPipeline af (parse (fileName, irFileContents)) ia
         & (if verbosity == Loud then PT.runTracePrint else PT.runTraceIgnore)
         & (\act -> runWriter act >>= appendToOutput)
         & runError
  case res of
    Left (err :: IodineException) -> E.throwIO err
    Right out -> (snd out,) <$> runPipeline ia out
  where
    appendToOutput (logs, result) = do
      unless (null logs) $ liftIO $
        withFile "debug-output" WriteMode $ \h ->
        traverse_ (hPutStrLn h) logs
      return result



main :: IO ()
main = do
  out <- runner
  writeFile "debug-output" $ show out
  analyze


readDebugOutput :: IO DebugOutput
readDebugOutput = read <$> readFile "debug-output"


debugArgs :: IO IodineArgs
debugArgs = do
  args <- getArgs
  case args of
    [] -> normalizeIodineArgs $ defaultIodineArgs
          { fileName    = debugVerilogFile
          , annotFile   = debugAnnotationFile
          , iverilogDir = "iverilog-parser"
          , verbosity   = iodineVerbosity
          , noSave      = disableFQSave
          }
    _ -> parseArgsWithError args


(!) :: (Eq k, Hashable k, Show k)
    => HM.HashMap k v -> k -> v
m ! k =
  case HM.lookup k m of
    Nothing -> error $ printf "Could not find %s in %s" (show k) (show $ HM.keys m)
    Just v -> v

trace' :: (Has (PT.Trace) sig m, Show a) => String -> a -> m ()
trace' msg a = PT.trace (msg ++ " " ++ show a)

analyze :: IO ()
analyze = do
  ((af, mm, sm), FQOutAnalysisOutput{..}) <- readDebugOutput
  let topModuleName = af ^. afTopModule
      m@Module{..}  = mm ! topModuleName
      inputs        = moduleInputs m mempty

      isCTVar i t = T.unpack t `elem` (ctVars IM.! i) || t `elem` inputs
      isAEVar i t = T.unpack t `elem` (aeVars IM.! i)
      isCTExpr i  = all (isCTVar i) . getVariables
      isAEExpr i  = all (isAEVar i) . getVariables

      go i Block{..}  = gos i blockStmts
      go i s          = gos i (return s)

      gos i SQ.Empty = return mempty
      gos i (s SQ.:<| ss) =
        case s of
          Block{..}     -> gos i $ blockStmts <> ss
          IfStmt{..}    ->
            if isAEExpr i ifStmtCondition
            then gos i (ifStmtThen <| ifStmtElse <| ss)
            else (s SQ.<|) <$> gos i ss
          Assignment{}  -> gos i ss
          Skip{}        -> gos i ss

  for_ alwaysBlocks $ \ab -> do
    let i = getData ab
    stmts <- go i $ abStmt ab
    let dc = defaultDocConfig
             { varColorMap = \n v -> if | isAEVar n v -> Just Green
                                        | isCTVar n v -> Just Blue
                                        | otherwise   -> Nothing
             , currentDocIndex = Just i
             }
    for_ stmts $ \s -> do
      printf "In always #%d %s\n" i (prettyShow $ abEvent ab)
      putStrLn $ prettyShowWithConfig dc s
      putStrLn $ replicate 80 '#'
      putStrLn ""

  let isCommon vm v = all (elem $ T.unpack v) vm
      isCommonCTVar = isCommon ctVars
      isCommonAEVar = isCommon aeVars
      dc = defaultDocConfig
           { varColorMap = \_ v -> if isCommonCTVar v then Nothing else Just Red
           , currentDocIndex = Just 0
           }
      abIds = getData <$> alwaysBlocks
      isCTExpr' v = all (`isCTExpr` v) abIds
  for_ moduleInstances $ \mi ->
    unless (all isCTExpr' $ moduleInstancePorts mi) $ do
      putStrLn $ prettyShowWithConfig dc mi
      putStrLn $ replicate 80 '#'
      putStrLn ""

  let ModuleSummary{..} = sm HM.! topModuleName
      addWriteId v = (v,) $ maybe (-1) IS.findMin $ HM.lookup (T.pack v) threadWriteMap
  for_ ctVarsDisagree $ \(n1, n2, vs) ->
    printf "Variables ct in %d but not in %d: %s\n"
    n1 n2 (show $ addWriteId <$> toList vs)
  for_ aeVarsDisagree $ \(n1, n2, vs) ->
    printf "Variables ae in %d but not in %d: %s\n"
    n1 n2 (show $ addWriteId <$> toList vs)