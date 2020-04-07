{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
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

import qualified Control.Exception as E
import           Control.Lens
import           Control.Monad
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
import           Polysemy hiding (run)
import           Polysemy.Error
import           Polysemy.Output
import           Polysemy.Reader
import           Polysemy.State
import qualified Polysemy.Trace as PT
import           System.Directory
import           System.Environment
import           System.FilePath.Posix
import           System.IO.Error
import           Text.PrettyPrint.HughesPJ (render)
import           Text.Printf

-- #############################################################################
-- Debug Configuration
-- #############################################################################
-- | iodine arguments
enableVerbose = True
disableFQSave = False

-- debugVerilogFile = "benchmarks" </> "yarvi" </> "shared" </> "test-01.v"
-- debugAnnotationFile = defaultAnnotFile debugVerilogFile
debugVerilogFile = "benchmarks" </> "yarvi" </> "shared" </> "yarvi.v"
debugAnnotationFile = "benchmarks" </> "yarvi" </> "shared" </> "annot-yarvi_fixed.json"

-- | this is the code that runs after the vcgen step
debug :: D r => Debug4 r
debug = debug4

-- | takes the iodine args and successful result of the 'debug' as an input
runPipeline :: RunFixpoint
runPipeline = runFixpoint
-- #############################################################################


allRegisterDependencies :: D r => Id -> Id -> Sem r Ids
allRegisterDependencies mn var = do
  Module{..} <- asks (! mn)
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

printThreadDeps :: D r => Sem r ()
printThreadDeps = do
  ModuleSummary{..} <- asks (! "mips_pipeline")
  output $ printGraph threadDependencies show

getCondVars :: L (AlwaysBlock Int) -> Sem r Ids
getCondVars as = execState mempty $ do
  let goStmt = \case
        Block{..} -> traverse_ goStmt blockStmts
        Assignment{..} -> return ()
        IfStmt{..} -> do
          modify (HS.union $ getVariables ifStmtCondition)
          goStmt ifStmtThen
          goStmt ifStmtElse
        Skip{} -> return ()
  traverse_ goStmt (abStmt <$> as)

getMissingInitialEquals :: (D r, Members '[Reader (HM.HashMap Id Ids)] r)
                        => Module Int -> Sem r Ids
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

debug1 :: D r => Sem r ()
debug1 = do
  ModuleSummary{..} <- asks (! "mux3")
  PT.trace $ show portDependencies
  PT.trace $ show isCombinatorial

debug2 :: D r => Sem r ()
debug2 = do
  ir <- ask @IRs
  allIEs <- computeAllInitialEqualVars ir
  traverse_ getMissingInitialEquals ir
    & runReader allIEs

debug3 :: D r => Sem r ()
debug3 = do
  ModuleSummary{..} <- asks (! "yarvi")
  PT.trace $
    printGraph threadDependencies (\n -> "#" <> show n)

type Debug4 r = VCGenOutput -> Sem r PipelineData
debug4 :: D r => Debug4 r
debug4 vcOut = do
  modules <- ask
  finfo <- constructQuery modules vcOut
  (finfo,) <$> ((,,) <$> ask <*> ask <*> ask)



type IRs = L (Module Int)
type ModuleMap = HM.HashMap Id (Module Int)
type G r  = Members '[Error IodineException, PT.Trace, Output String] r
type D r = ( G r
           , Members '[ Reader AnnotationFile
                      , Reader ModuleMap
                      , Reader SummaryMap
                      , Reader IRs
                      ] r
           )

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


run :: IO DebugOutput
run = do
  (ia@IodineArgs{..}, af) <- debugArgs >>= generateIR
  irFileContents <- readIRFile fileName
  r <- tryIOError $ removeFile outputFile
  case r of
    Right _ -> return ()
    Left e -> unless (isDoesNotExistError e) $ E.throwIO e
  res <- debugPipeline af (parse (fileName, irFileContents)) ia
    & (if verbose then PT.traceToIO else PT.ignoreTrace)
    & errorToIOFinal
    & runOutputSem (embed . appendFile outputFile) & embedToFinal & runFinal
  case res of
    Left err  -> E.throwIO err
    Right out -> (snd out,) <$> runPipeline ia out
  where
    outputFile = "debug-output"


main :: IO ()
main = do
  out <- run
  writeFile "debug-output" $ show out
  analyze


readDebugOutput :: IO DebugOutput
readDebugOutput = read <$> readFile "debug-output"


debugArgs :: IO IodineArgs
debugArgs = do
  args <- getArgs
  case args of
    [] -> do ivd <- makeAbsolute "iverilog-parser"
             vf  <- makeAbsolute debugVerilogFile
             af  <- makeAbsolute debugAnnotationFile
             return $ defaultIodineArgs
               { fileName    = vf
               , annotFile   = af
               , iverilogDir = ivd
               , verbose     = enableVerbose
               , noSave      = disableFQSave
               }
    _ -> parseArgsWithError args


(!) :: (Eq k, Hashable k, Show k)
    => HM.HashMap k v -> k -> v
m ! k =
  case HM.lookup k m of
    Nothing -> error $ printf "Could not find %s in %s" (show k) (show $ HM.keys m)
    Just v -> v

trace' :: (Members '[PT.Trace] r, Show a) => String -> a -> Sem r ()
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
      go i s          = gos i (mempty |> s)

      gos i SQ.Empty = return SQ.empty
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
      putStrLn $ prettyShowWithConfig dc s
      putStrLn $ replicate 80 '#'

  let isCommonCTVar v = all (elem $ T.unpack v) ctVars
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

  for_ ctVarsDisagree $ \(n1, n2, vs) ->
    printf "%d and %d disagree on: %s\n" n1 n2 (show $ toList vs)
