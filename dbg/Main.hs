{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import           Iodine.Analyze.FQOutAnalysis
import           Iodine.Analyze.ModuleSummary
import           Iodine.Analyze.DependencyGraph
import           Iodine.IodineArgs
import qualified Iodine.IodineArgs             as IA
import           Iodine.Language.Annotation
import           Iodine.Language.IR            as IR
import           Iodine.Language.IRParser
import           Iodine.Pipeline                ( normalizeIR )
import           Iodine.Runner                  ( generateIR
                                                , readIRFile
                                                )
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
import           Control.Carrier.Trace.Print    ( Trace )
import qualified Control.Carrier.Trace.Print   as PT
import           Control.Carrier.Writer.Strict
import qualified Control.Exception             as E
import           Control.Lens
import           Control.Applicative
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Bifunctor
import           Data.Foldable
import qualified Data.Graph.Inductive          as G
import qualified Data.Graph.Inductive.Dot      as GD
import qualified Data.HashMap.Strict           as HM
import qualified Data.HashSet                  as HS
import           Data.Hashable
import qualified Data.IntMap                   as IM
import qualified Data.IntSet                   as IS
import           Data.Maybe
import qualified Data.Sequence                 as SQ
import qualified Data.Text                     as T
import qualified Language.Fixpoint.Misc        as FM
import qualified Language.Fixpoint.Solver      as F
import qualified Language.Fixpoint.Solver.Monad
                                               as FSM
import qualified Language.Fixpoint.Types       as FT
import qualified Language.Fixpoint.Types.Config
                                               as FC
import           System.Directory
import           System.Environment
import           System.FilePath.Posix
import           System.IO
import           System.IO.Error
import           Text.PrettyPrint.HughesPJ      ( render )
import qualified Text.PrettyPrint.HughesPJ     as PP
import           Text.Printf
import           GHC.Generics            hiding ( to
                                                , D
                                                , moduleName
                                                )
import qualified Debug.Trace                   as DT
import           System.Process

-- #############################################################################
-- Debug Configuration
-- #############################################################################
-- | iodine arguments
iodineVerbosity = Loud
disableFQSave = False

-- debugVerilogFile = "benchmarks" </> "yarvi" </> "shared" </> "test-01.v"
-- debugAnnotationFile = defaultAnnotFile debugVerilogFile
debugVerilogFile = "benchmarks" </> "yarvi" </> "shared" </> "yarvi.v"
debugAnnotationFile =
  "benchmarks" </> "yarvi" </> "shared" </> "annot-yarvi_fixed.json"

-- | this is the code that runs after the vcgen step
debug :: D sig m => Debug4 sig m
debug = debug4

-- | takes the iodine args and successful result of the 'debug' as an input
runPipeline :: RunFixpoint
runPipeline = runFixpoint
-- #############################################################################


allRegisterDependencies :: D sig m => Id -> Id -> m Ids
allRegisterDependencies mn var = do
  Module {..}        <- asks @ModuleMap (! mn)
  ModuleSummary {..} <- asks (! mn)
  -- trace' "variables" (toList variables)
  let g     = variableDependencies
      toId  = (variableDependencyNodeMap !)
      toVar = (invVariableDependencyNodeMap IM.!)
      -- varNo = toId var
  -- trace ("pre of " ++ T.unpack var ++ " " ++ show varNo) (first toVar <$> G.lpre g varNo)
  -- trace ("pre of " ++ T.unpack var) (G.lpre g (toId var))
  let
    isReg r = Register r `elem` variables
    wl regs _       SQ.Empty      = return regs
    wl regs history (n SQ.:<| ns) = -- do
      -- trace' "wl" (regs, history, n, ns)
                                    if IS.member n history
      then wl regs history ns
      else do
        let history' = IS.insert n history
            ps =
              SQ.filter (not . (`IS.member` history)) $ toSequence $ G.pre g n
            nv           = toVar n
            (regs', ns') = if isReg nv
              then (HS.insert nv regs, ns)
              else foldl'
                (\(rs, vns) vn ->
                  let v = toVar vn
                  in  if isReg v
                        then (HS.insert v rs, ns)
                        else (rs, vns SQ.|> vn)
                )
                (regs, ns)
                ps
        -- trace' "vn" (toVar n)
        -- trace' "ps" (toVar <$> ps)
        -- trace' "ps'" (toVar <$> G.pre g n)
        wl regs' history' ns'
  let varId     = toId var
      preVarIds = toSequence $ G.pre g varId
  wl mempty mempty preVarIds
  -- regDeps <- wl mempty mempty preVarIds
  -- trace
  --   (printf "register dependencies of %s in module %s" var mn)
  --   regDeps
  -- return regDeps

printThreadDeps :: D sig m => m ()
printThreadDeps = do
  ModuleSummary {..} <- asks @SummaryMap (! "mips_pipeline")
  output [printGraph threadDependencies show]

getCondVars as = execState @Ids mempty $ do
  let goStmt = \case
        Block {..}      -> traverse_ goStmt blockStmts
        Assignment {..} -> return ()
        IfStmt {..}     -> do
          modify (HS.union $ getVariables ifStmtCondition)
          goStmt ifStmtThen
          goStmt ifStmtElse
        Skip{} -> return ()
  traverse_ goStmt (abStmt <$> as)

getMissingInitialEquals Module {..} = do
  PT.trace $ printf "getMissingInitialEquals - %s" moduleName
  allInitEqs :: Ids <- asks (HM.! moduleName)
  let isInitEq = (`elem` allInitEqs)
  registersThatAffectConditions <-
    fold
      <$> (toSequence <$> getCondVars alwaysBlocks >>= traverse
            (allRegisterDependencies moduleName)
          )
  trace "registers that affect conditions"
        (HS.toList registersThatAffectConditions)
  let missingRegs = HS.filter (not . isInitEq) registersThatAffectConditions
  trace "missing registers" (moduleName, HS.toList missingRegs)
  return missingRegs

debug1 :: D sig m => m ()
debug1 = do
  ModuleSummary {..} <- asks @SummaryMap (! "mux3")
  PT.trace $ show portDependencies
  PT.trace $ show isCombinatorial

debug2 :: D sig m => m ()
debug2 = do
  ir     <- ask @IRs
  allIEs <- computeAllInitialEqualVars ir
  traverse_ getMissingInitialEquals ir & runReader allIEs

debug3 :: D sig m => m ()
debug3 = do
  ModuleSummary {..} <- asks @SummaryMap (! "yarvi")
  PT.trace $ printGraph threadDependencies (\n -> "#" <> show n)

type Debug4 sig m = VCGenOutput -> m PipelineData
debug4 :: D sig m => Debug4 sig m
debug4 vcOut = do
  modules <- ask
  finfo   <- constructQuery modules vcOut
  (finfo, ) <$> ((,,) <$> ask <*> ask <*> ask)

type A = Int
type M = Module A
type IRs = L (Module Int)
type ModuleMap = HM.HashMap Id (Module Int)
type G sig m
  = ( Has (Error IodineException) sig m
    , Has Trace sig m
    , Has (Writer Output) sig m
    )
               -- , Effect sig
type D sig m
  = ( G sig m
    , Has (Reader AnnotationFile) sig m
    , Has (Reader ModuleMap) sig m
    , Has (Reader SummaryMap) sig m
    , Has (Reader IRs) sig m
    )

type IRReaderM = PT.TraceC (WriterC Output (ErrorC IodineException IO))

debugPipeline
  :: AnnotationFile
  -> IRReaderM (L (Module ()))
  -> IodineArgs
  -> IRReaderM PipelineData
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

type ModuleSummaries = HM.HashMap Id [FSM.TraceQualif]
type PipelineData = (FInfo, PipelineData2)
type PipelineData2 = (AnnotationFile, ModuleMap, SummaryMap)
type RunFixpoint
  = IodineArgs -> PipelineData -> IO (FQOutAnalysisOutput, ModuleSummaries)
type DebugOutput = (PipelineData2, FQOutAnalysisOutput, ModuleSummaries)

runFixpoint :: RunFixpoint
runFixpoint IodineArgs {..} (finfo, (af, mm, sm)) = do
  result <- F.solve config finfo
  let toSummaries (FT.PAnd es) = catMaybes (FSM.toTraceSummary <$> es)
      toSummaries _            = undefined
  let moduleKvarNos = HM.fromList $ HM.foldlWithKey'
        (\acc name m ->
          let toK :: GetData m => m Int -> (String, Id)
              toK k = ("inv" ++ show (getData k), name)
              k1   = toK m
              abks = foldl' (\acc2 ab -> toK ab : acc2) [] (alwaysBlocks m)
          in  k1 : abks ++ acc
        )
        []
        mm
  let moduleSummaries =
        HM.fromList
          $   filter (not . null . snd)
          $   fmap (bimap (moduleKvarNos HM.!) toSummaries)
          $   filter ((`HM.member` moduleKvarNos) . fst)
          $   first (FT.symbolSafeString . FT.kv)
          <$> HM.toList (FT.resSolution result)
  let stat    = FT.resStatus result
      statStr = render . FT.resultDoc
  FM.colorStrLn (FT.colorResult stat) (statStr stat)
  (, moduleSummaries) <$> findFirstNonCTVars result af mm sm
 where
  config = FC.defConfig { FC.eliminate   = FC.Some
                        , FC.save        = not noSave
                        , FC.srcFile     = fileName
                        , FC.metadata    = True
                        , FC.minimize    = delta
                        , FC.solverTrace = True
                        }


runner :: IO DebugOutput
runner = do
  (ia@IodineArgs {..}, af) <- debugArgs >>= generateIR
  irFileContents           <- readIRFile ia fileName
  res                      <-
    debugPipeline af (parse (fileName, irFileContents)) ia
    & (if verbosity == Loud then PT.runTracePrint else PT.runTraceIgnore)
    & (runWriter >=> appendToOutput)
    & runError
  case res of
    Left (err :: IodineException) -> E.throwIO err
    Right out -> (\(x, y) -> (snd out, x, y)) <$> runPipeline ia out
 where
  appendToOutput (logs, result) = do
    unless (null logs) $ liftIO $ withFile "debug-output" WriteMode $ \h ->
      traverse_ (hPutStrLn h) logs
    return result


main :: IO ()
main = do
  out <- runner
  writeFile "debug-output" $ show out
  analyze

readDebugOutput :: IO DebugOutput
readDebugOutput = read <$> readFile "debug-output"

readFixpointTrace :: IO FSM.SolverTrace
readFixpointTrace = FSM.readSolverTrace "fixpoint-trace.json"

calculateSolverTraceDiff :: FSM.SolverTrace -> FSM.SolverTrace
calculateSolverTraceDiff st =
  IM.fromList $ filter (not . HM.null . snd) $ diffPairs <$> pairs
 where
  mkPairs = zip <$> id <*> tail
  pairs   = mkPairs $ IM.toList st
  diffPairs ((_, te1), (n2, te2)) =
    (n2, HM.filter (not . HS.null) $ teDiff te1 te2)
  qFilter = \case
    FSM.TracePublic       _ -> True
    FSM.TraceUntainted    _ -> True
    FSM.TraceConstantTime _ -> True
    FSM.TraceSameTaint _ _  -> False
    FSM.TraceSummary   _ _  -> False
  teDiff te1 = HM.mapWithKey $ \kv qs2 ->
    HS.filter qFilter $ case HM.lookup kv te1 of
      Nothing  -> qs2
      Just qs1 -> HS.difference qs1 qs2

data QualType = Q_CT | Q_PUB deriving (Show, Eq, Generic)

instance Hashable QualType

-- type SolverTraceElement = M.HashMap T.Text Qs
-- type SolverTrace = IM.IntMap SolverTraceElement

-- variable name -> kvar no -> QualType -> first non ct
type BetterTraceMap = HM.HashMap T.Text (IM.IntMap (HM.HashMap QualType Int))

firstNonCT :: FSM.SolverTrace -> BetterTraceMap
firstNonCT = IM.foldlWithKey' handleTraceElem mempty
 where
  handleTraceElem acc iterNo = HM.foldl' (handleKVar iterNo) acc
  handleKVar iterNo = HS.foldl' (handleQ iterNo)
  handleQ iterNo acc = \case
    FSM.TraceConstantTime tv -> updateAcc tv Q_CT iterNo acc
    FSM.TracePublic       tv -> updateAcc tv Q_PUB iterNo acc
    _                        -> acc
  updateAcc (FSM.TraceVar _ varName kvarNo) qTyp iterNo acc =
    let qm = HM.fromList [(qTyp, iterNo)]

        f1 Nothing  = IM.fromList [(kvarNo, qm)]
        f1 (Just m) = IM.alter (Just . f2) kvarNo m

        f2 Nothing    = qm
        f2 (Just qm2) = HM.alter (Just . f3) qTyp qm2

        f3 Nothing  = iterNo
        f3 (Just n) = min n iterNo
    in  HM.alter (Just . f1) (T.pack varName) acc

type TstG = G.Gr Int VarDepEdgeType

tst :: IO ()
tst = do
  ((af, moduleMap, summaryMap), fqoutAnalysisOutput, moduleSummaries) <-
    readDebugOutput
  fpTrace <- readFixpointTrace
  let btm = firstNonCT $ calculateSolverTraceDiff fpTrace
  let
    topmoduleName = af ^. afTopModule

    snks = HS.toList $ view (moduleAnnotations . sinks) $ toModuleAnnotations
      topmoduleName
      af

    topModule = fromJust $ moduleMap ^. at topmoduleName
    moduleSummary@ModuleSummary {..} =
      fromJust $ summaryMap ^. at topmoduleName

    toNode = (variableDependencyNodeMap HM.!)
    toName = (invVariableDependencyNodeMap IM.!)

    trc :: Show a => String -> a -> a
    trc msg a = DT.trace (msg ++ show a) a

    getWriteTid :: Id -> Int
    getWriteTid varName = fromJust $ threadWriteMap ^. at varName

    btmLookup :: QualType -> Id -> Maybe Int
    btmLookup qt varName = do
      kvs <- trc (printf "getCTNo qs (%s): " varName) $ btm ^. at varName
      case IM.toList kvs of
        [(tid, m)] -> m ^. at qt
        qsList ->
          case
              [ (tid, iterNo)
              | (tid, qs    ) <- qsList
              , (qt', iterNo) <- HM.toList qs
              , qt' == qt
              ]
            of
              []              -> Nothing
              [(tid, iterNo)] -> Just iterNo
              iterNos         -> error $ "Multiple iterNos: " ++ show iterNos

    getCTNo = btmLookup Q_CT

    insNode n a g = if G.gelem n g then g else G.insNode (n, a) g

    insEdge' e@(n1, n2, edgeType) g =
      if n1 `elem` G.reachable n2 g then g else insEdge e g

    getDeps v = getVariableDependencies v topModule summaryMap

    createDepTree :: (Id -> Maybe Int) -> (Int -> Int -> Bool) -> TstG -> Id -> Ids -> (TstG, Ids)
    createDepTree getIterNo iterNoCmp g parentName ws
      | HS.member parentName ws
      = (g, ws)
      | otherwise
      = case trc (printf "parentCtNo (%s): " parentName) $ getIterNo parentName of
        Nothing -> (g, ws)
        Just parentIterNo ->
          let
            parentNode    = toNode parentName
            childrenNodes = trc "childrenNodes: " $ getDeps parentName
            nonCTChildren =
              [ (childName, fromJust childIterNo, depType)
              | (childName, depType) <- childrenNodes
              , let
                childIterNo =
                  trc (printf "childCtNo (%s) : " childName) $ getIterNo childName
              , isJust childIterNo
              ]
            go acc@(g2, ws2) (childName, childIterNo, edgeType) =
              if iterNoCmp childIterNo parentIterNo
              then
                let
                  childNode = toNode childName
                  e = (parentNode, childNode, edgeType)
                  g3 = insEdge' e $ insNode parentNode parentIterNo $ insNode
                    childNode
                    childIterNo
                    g2
                in
                  createDepTree getIterNo iterNoCmp g3 childName ws2
              else acc
            acc' = (g, HS.insert parentName ws)
          in
            foldl' go acc' nonCTChildren

  print snks
  let createSinkTree = createDepTree getCTNo (<=)
  let nonCtTree = fst $ foldl' (\(g, ws) snk -> createSinkTree g snk ws)
                               (G.empty, mempty)
                               snks
  let
    toDotStr = GD.showDot . GD.fglToDot . G.gmap
      (\(ps, n, i, ss) ->
        let lbl =
                T.unpack (invVariableDependencyNodeMap IM.! n) ++ " " ++ show i
        in  (ps, n, lbl, ss)
      )
  writeFile "graph.dot" $ toDotStr nonCtTree
  system "dot -Tpdf graph.dot -o graph.pdf"

  let lastTraceElem = snd . fromJust $ IM.lookupMax fpTrace
  let isPublic varName =
        let v = T.unpack varName
            helper (FSM.TracePublic (FSM.TraceVar _ tv _)) = tv == v
            helper _ = False
        in any (any helper) lastTraceElem
  let getPubNo v = btmLookup Q_PUB v <|> if isPublic v then Nothing else Just 0
  let getLeaves g =
        foldl' (\acc n -> if G.outdeg g n == 0 then n : acc else acc) []
          $ G.nodes nonCtTree
  let nonCtTreeLeaves = toName <$> getLeaves nonCtTree
      hasToBePublic = HS.fromList $
        [ childName
        | leaf <- nonCtTreeLeaves
        , (childName, depType) <- getDeps leaf
        , depType == Implicit
        , isJust $ getPubNo childName
        ]
  print nonCtTreeLeaves
  print $ getDeps <$> nonCtTreeLeaves
  print hasToBePublic
  let createPubTree = createDepTree getPubNo (\_ _ -> True)
  let nonPubTree = fst $ foldl' (\(g, ws) v -> createPubTree g v ws) (G.empty, mempty) hasToBePublic
  writeFile "graph2.dot" $ toDotStr nonPubTree
  system "dot -Tpdf graph2.dot -o graph2.pdf"

  -- flip HM.traverseWithKey moduleSummaries $ \k qs -> do
  --   print k
  --   printSummaries qs
  --   putStrLn ""

  return ()

printSummaries :: [FSM.TraceQualif] -> IO ()
printSummaries = traverse_ go
 where
  go (FSM.TraceSummary es1 es2) = do
    putStr "["
    traverse_ go2 es1
    putStr "] => ["
    traverse_ go2 es2
    putStrLn "]"
  go _ = undefined

  toV (FSM.TraceVar _ v _) = v

  go2 (FSM.TracePublic       v) = printf "public(%s), " (toV v)
  go2 (FSM.TraceConstantTime v) = printf "ct(%s), " (toV v)
  go2 _                         = undefined


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


(!) :: (Eq k, Hashable k, Show k) => HM.HashMap k v -> k -> v
m ! k = case HM.lookup k m of
  Nothing ->
    error $ printf "Could not find %s in %s" (show k) (show $ HM.keys m)
  Just v -> v

trace' :: (Has PT.Trace sig m, Show a) => String -> a -> m ()
trace' msg a = PT.trace (msg ++ " " ++ show a)

analyze :: IO ()
analyze = do
  ((af, mm, sm), FQOutAnalysisOutput {..}, moduleSummaries) <- readDebugOutput
  let topModuleName = af ^. afTopModule
      m@Module {..} = mm ! topModuleName
      inputs        = moduleInputs m mempty

      isCTVar i t = T.unpack t `elem` (ctVars IM.! i) || t `elem` inputs
      isAEVar i t = T.unpack t `elem` (aeVars IM.! i)
      isCTExpr i = all (isCTVar i) . getVariables
      isAEExpr i = all (isAEVar i) . getVariables

      go i Block {..} = gos i blockStmts
      go i s          = gos i (return s)

      gos i SQ.Empty      = return mempty
      gos i (s SQ.:<| ss) = case s of
        Block {..}  -> gos i $ blockStmts <> ss
        IfStmt {..} -> if isAEExpr i ifStmtCondition
          then gos i (ifStmtThen <| ifStmtElse <| ss)
          else (s SQ.<|) <$> gos i ss
        Assignment{} -> gos i ss
        Skip{}       -> gos i ss

  for_ alwaysBlocks $ \ab -> do
    let i = getData ab
    stmts <- go i $ abStmt ab
    let dc = defaultDocConfig
          { varColorMap     = \n v -> if
                                | isAEVar n v -> Just Green
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
      dc            = defaultDocConfig
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

  let ModuleSummary {..} = sm HM.! topModuleName
      addWriteId v =
        (v, ) $ fromMaybe (-1) $ HM.lookup (T.pack v) threadWriteMap

  for_ ctVarsDisagree $ \(n1, n2, vs) -> do
    let varWithUpdateThreads = addWriteId <$> toList vs
    printf "Variables ct in %d but not in %d:\n%s\n"
           n1
           n2
           (prettyList varWithUpdateThreads)
    printf "Vars not updated by %d:\n%s\n"
           n1
           (prettyList $ filter ((/= n1) . snd) varWithUpdateThreads)
    putStrLn $ replicate 80 '-'

  for_ aeVarsDisagree $ \(n1, n2, vs) -> do
    let varWithUpdateThreads = addWriteId <$> toList vs
    printf "Variables ae in %d but not in %d:\n%s\n"
           n1
           n2
           (prettyList varWithUpdateThreads)
    printf "Vars not updated by %d:\n%s\n"
           n1
           (prettyList $ filter ((/= n1) . snd) varWithUpdateThreads)
    putStrLn $ replicate 80 '-'

prettyList :: (Show a, Foldable t) => t a -> String
prettyList l = PP.render d
 where
  d = PP.sep
    [ PP.lbrack
    , PP.sep $ PP.punctuate PP.comma $ PP.text . show <$> toList l
    , PP.rbrack
    ]

printThreadGraph :: IO ()
printThreadGraph = do
  dbgo <- readDebugOutput
  let mn = dbgo ^. _1 . _1 . afTopModule
  let g = dbgo ^. _1 . _3 . at "yarvi" . to (threadDependencies . fromJust)
  writeFile "graph.dot" $ printGraph g show

printThreads :: IO ()
printThreads = do
  dbgo <- readDebugOutput
  let mn = dbgo ^. _1 . _1 . afTopModule
  let Module {..} = fromJust $ dbgo ^. _1 . _2 . at mn
      h :: IR.Doc a => a Int -> IO ()
      h = putStrLn . head . lines . prettyShow
  traverse_ h alwaysBlocks
  traverse_ h moduleInstances
