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
import           Iodine.Transform.Fixpoint.Common (HornClauseId)

import           Control.Carrier.Error.Either
import           Control.Carrier.Reader
import           Control.Carrier.Lift
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
import           Data.List
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
import           System.Exit
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
iodineVerbosity :: Verbosity
iodineVerbosity = Loud
disableFQSave :: Bool
disableFQSave = False

-- debugVerilogFile = "benchmarks" </> "yarvi" </> "shared" </> "test-01.v"
-- debugAnnotationFile = defaultAnnotFile debugVerilogFile
debugVerilogFile :: FilePath
debugVerilogFile = "benchmarks" </> "yarvi" </> "shared" </> "yarvi.v"
debugAnnotationFile :: FilePath
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

getCondVars :: (Foldable t, Functor t, Algebra sig m) => t (AlwaysBlock a) -> m Ids
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

getMissingInitialEquals :: ( D sig m
                           , Has (Reader (HM.HashMap Id Ids)) sig m
                           )
                        => Module a
                        -> m (HS.HashSet Id)
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
  let constraintTypes =
        IM.fromList $ fmap (bimap fromIntegral FT.sinfo) $ HM.toList $ FT.cm finfo
  (finfo, constraintTypes, ) <$> ((,,) <$> ask <*> ask <*> ask)

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

runDefaultPipeline :: Monad m => p -> m ()
runDefaultPipeline _ = return ()

type ConstraintTypes = IM.IntMap HornClauseId
type FixpointResult = FT.Result (Integer, HornClauseId)
type ModuleSummaries = HM.HashMap Id [FSM.TraceQualif]
type PipelineData = (FInfo, ConstraintTypes, PipelineData2)
type PipelineData2 = (AnnotationFile, ModuleMap, SummaryMap)
type RunFixpoint = IodineArgs -> PipelineData -> IO (FixpointResult, FQOutAnalysisOutput, ModuleSummaries)
type DebugOutput = (PipelineData2, ConstraintTypes, FQOutAnalysisOutput, ModuleSummaries)

runFixpoint :: RunFixpoint
runFixpoint IodineArgs {..} (finfo, cm, (af, mm, sm)) = do
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
  (result, , moduleSummaries) <$> findFirstNonCTVars result af mm sm
 where
  config = FC.defConfig { FC.eliminate   = FC.Some
                        , FC.save        = not noSave
                        , FC.srcFile     = fileName
                        , FC.metadata    = True
                        , FC.minimize    = delta
                        , FC.solverTrace = True
                        }


runner :: IO (Bool, DebugOutput)
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
    Right out@(_, cm, z) -> (\(r, x, y) -> (FT.isSafe r, (z, cm, x, y))) <$> runPipeline ia out
 where
  appendToOutput (logs, result) = do
    unless (null logs) $ liftIO $ withFile "debug-output" WriteMode $ \h ->
      traverse_ (hPutStrLn h) logs
    return result


main :: IO ()
main = do
  (isSafe, out) <- runner
  writeFile "debug-output" $ show out
  -- analyze
  print isSafe

readDebugOutput :: IO DebugOutput
readDebugOutput = read <$> readFile "debug-output"

readFixpointTrace :: IO FSM.SolverTrace
readFixpointTrace = FSM.readSolverTrace "fixpoint-trace.json"

type SolverTrace = IM.IntMap FSM.SolverTraceElement

calculateSolverTraceDiff :: FSM.SolverTrace -> FSM.SolverTrace
calculateSolverTraceDiff st =
  IM.fromList $ filter (not . HM.null . snd . snd) $ diffPairs <$> pairs
 where
  mkPairs = zip <$> id <*> tail
  pairs   = mkPairs $ IM.toList st
  diffPairs ((_, (_, te1)), (n2, (c2, te2))) =
    (n2, (c2, HM.filter (not . HS.null) $ teDiff te1 te2))
  qFilter = \case
    FSM.TracePublic       _ -> True
    FSM.TraceUntainted    _ -> True
    FSM.TraceConstantTime _ -> True
    FSM.TraceSameTaint _ _  -> False
    FSM.TraceSummary   _ _  -> False
  teDiff te1 = HM.mapWithKey $ \kv qs2 ->
    HS.filter qFilter $ case HM.lookup kv te1 of
      Nothing  -> mempty
      Just qs1 -> HS.difference qs1 qs2

data QualType = Q_CT | Q_PUB deriving (Show, Eq, Generic)

instance Hashable QualType

-- type SolverTraceElement = M.HashMap T.Text Qs
-- type SolverTrace = IM.IntMap SolverTraceElement

-- variable name -> kvar no -> QualType -> first non ct
type BetterTraceMap = HM.HashMap T.Text (IM.IntMap (HM.HashMap QualType Int))

nonCTVars :: Module Int -> BetterTraceMap -> [(Id, Int)]
nonCTVars Module{..} btm =
  let threadIds = (getData <$> alwaysBlocks) <> (getData <$> moduleInstances)
      allIndices =
        [ (v, n)
        | (v, im) <- HM.toList btm
        , any (`elem` threadIds) (IM.keys im)
        , let m = foldl' (HM.unionWith min) mempty (IM.elems im)
        , n <- toList $ HM.lookup Q_CT m
        ]
  in sortOn snd allIndices

firstNonCTVars :: Module Int -> BetterTraceMap -> [(Id, Int)]
firstNonCTVars m btm =
  let sortedIndices = nonCTVars m btm
      minIndex = snd $ head sortedIndices
  in filter ((== minIndex) . snd) sortedIndices

firstNonCT :: FSM.SolverTrace -> BetterTraceMap
firstNonCT = IM.foldlWithKey' handleTraceElem mempty . fmap snd
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

toTVName :: FSM.TraceVar -> String
toTVName (FSM.TraceVar _ tv _) = tv

qualifMentionsVar :: String -> FSM.TraceQualif -> Bool
qualifMentionsVar varName = \case
  FSM.TracePublic tv         -> toTVName tv == varName
  FSM.TraceConstantTime tv   -> toTVName tv == varName
  FSM.TraceUntainted tv      -> toTVName tv == varName
  FSM.TraceSameTaint tv1 tv2 -> varName `elem` (toTVName <$> [tv1,tv2])
  FSM.TraceSummary _ _       -> False


btmLookup :: BetterTraceMap -> QualType -> Id -> Maybe Int
btmLookup btm qt varName = do
  kvs <- {- trc (printf "getCTNo qs (%s): " varName) $ -} btm ^. at varName
  case IM.toList kvs of
    [(tid, m)] -> m ^. at qt
    qsList ->
      case
          [ iterNo
          | (tid, m) <- qsList
          , iterNo <- toList $ HM.lookup qt m
          ]
        of
          []   -> Nothing
          i:is ->
            DT.trace (printf "Multiple iterNos for %s: %s" varName (show $ i:is)) $
            Just $ foldl' min i is

type TstG = G.Gr Int VarDepEdgeType

tst :: IO ()
tst = do
  ((af, moduleMap, summaryMap), cm, fqoutAnalysisOutput, moduleSummaries) <-
    readDebugOutput
  fpTrace <- readFixpointTrace
  let lastTraceElem = snd . snd . fromJust $ IM.lookupMax fpTrace
  let directLookup v =
        let helper = \case
              FSM.TracePublic tv -> toTVName tv == v
              FSM.TraceConstantTime tv -> toTVName tv == v
              _ -> False
        in [ (iterNo, kv, qs')
           | (iterNo, (_, m)) <- IM.toList fpTrace
           , (kv, qs) <- HM.toList m
           , let qs' = filter helper $ HS.toList qs
           , not (null qs')
           -- , any (any helper) m
           ]
  let btm = firstNonCT $ calculateSolverTraceDiff fpTrace
  let
    topmoduleName = af ^. afTopModule
    topmoduleAnnots = toModuleAnnotations topmoduleName af ^. moduleAnnotations
    snks = HS.toList $ topmoduleAnnots ^. sinks

    topModule = fromJust $ moduleMap ^. at topmoduleName
    moduleSummary@ModuleSummary {..} =
      fromJust $ summaryMap ^. at topmoduleName

    toNode = (variableDependencyNodeMap HM.!)
    toName = (invVariableDependencyNodeMap IM.!)

    trc :: Show a => String -> a -> a
    trc msg a = DT.trace (msg ++ show a) a

    getWriteTid :: Id -> Int
    getWriteTid varName = fromJust $ threadWriteMap ^. at varName

    isCT varName =
      let v = T.unpack varName
          helper (FSM.TraceConstantTime tv) = toTVName tv == v
          helper _ = False
      in any (any helper) lastTraceElem
    getCTNo v = btmLookup btm Q_CT v <|> if isCT v then Nothing else Just 0

    insNode n a g = if G.gelem n g then g else G.insNode (n, a) g

    insEdge' e@(n1, n2, edgeType) g =
      if n1 `elem` G.reachable n2 g then g else insEdge e g

    getDeps v = getVariableDependencies v topModule summaryMap

    createDepTree :: (Id -> Maybe Int) -> TstG -> Id -> Id -> Ids -> (TstG, Ids)
    createDepTree getIterNo g currentVarName _parentName ws
      | HS.member currentVarName ws
      = (g, ws)
      | otherwise
      = let parentName = currentVarName in case {- trc (printf "parentCtNo (%s): " currentVarName) $ -} getIterNo parentName of
        Nothing -> (g, ws)
        Just parentIterNo ->
          let
            childrenNodes = {- trc (printf "childrenNodes of %s: " currentVarName) $ -} getDeps currentVarName
            nonCTChildren =
              [ (childName, fromJust childIterNo, depType)
              | (childName, depType) <- childrenNodes
              , let
                childIterNo =
                  trc (printf "childCtNo (%s) : " childName) $ getIterNo childName
              , isJust childIterNo
              ]
            -- FIXME
            go acc@(g2, ws2) (childName, childIterNo, edgeType) =
              if childIterNo <= parentIterNo
              then
                let
                  childNode = toNode childName
                  parentNode = toNode parentName
                  e = (parentNode, childNode, edgeType)
                  g3 = insEdge' e $
                       insNode parentNode parentIterNo $
                       insNode childNode childIterNo g2
                in
                  createDepTree getIterNo g3 childName childName ws2
              else acc -- createDepTree getIterNo g2 childName parentName ws2
            acc' = (g, HS.insert currentVarName ws)
          in
            foldl' go acc' nonCTChildren

  print snks
  let createSinkTree = createDepTree getCTNo
  let
    toDotStr = GD.showDot . GD.fglToDot . G.gmap
      (\(ps, n, i, ss) ->
        let lbl =
                T.unpack (invVariableDependencyNodeMap IM.! n) ++ " " ++ show i
        in  (ps, n, lbl, ss)
      )
  let isPublic varName =
        let v = T.unpack varName
            helper (FSM.TracePublic tv) = toTVName tv == v
            helper _ = False
        in any (any helper) lastTraceElem
  let getPubNo v = btmLookup btm Q_PUB v <|> if isPublic v then Nothing else Just 0
  let getLeaves g =
        foldl' (\acc n -> if G.outdeg g n == 0 then n : acc else acc) []
          $ G.nodes g

  let hasToBePublic leaf = HS.fromList $
        [ (childName, fromJust pn)
        | (childName, depType) <- getDeps leaf
        , depType == Implicit
        , let pn = getPubNo childName
        , isJust pn
        ]
  let initTree = foldl' (\g (v, n) -> insNode (toNode v) n g) G.empty
  let nonCtTreeLoop roots initws =
        let (finalTree, finalWS) = foldl' (\(g, ws) (snk, _) -> createSinkTree g snk snk ws) (initTree roots, initws) roots
            nonCtTreeLeaves = toName <$> getLeaves finalTree
            allNonCtChildrenAreGreater l =
              let lIterNo = fromJust $ getCTNo l
                  childNos = getCTNo . fst <$> getDeps l
              in any (/= Nothing) childNos && all (maybe True (> lIterNo)) childNos
            needsFixin l = allNonCtChildrenAreGreater l && null (hasToBePublic l)
            rootsToFix = trc "rootsToFix: " $ filter needsFixin nonCtTreeLeaves
        -- FIXME
        in if True -- null rootsToFix
           then finalTree
           else
             let roots' = [ (c, n)
                          | r <- rootsToFix
                          , (c, _) <- getDeps r
                          , n <- toList $ getCTNo c
                          ]
             in nonCtTreeLoop roots' (foldl' (flip HS.delete) finalWS (fst <$> roots'))
  let nonCtTree = nonCtTreeLoop [(s,n) | s <- snks, n <- toList (getCTNo s)] mempty
  writeFile "graph.dot" $ toDotStr nonCtTree
  system "dot -Tpdf graph.dot -o graph.pdf"

  let shouldNotHaveCycle g msg =
        unless (length (G.nodes g) == length (G.scc g)) $ do
          putStrLn msg
          exitFailure

  shouldNotHaveCycle nonCtTree "ct tree has a cycle!"

  let createPubTree = createDepTree getPubNo
  let nonPubTreeRoots = [c | l <- getLeaves nonCtTree, c <- HS.toList (hasToBePublic $ toName l)]
  let nonPubTree =
        G.grev $ fst $
        foldl' (\(g, ws) (v, _) -> createPubTree g v v ws) (initTree nonPubTreeRoots, mempty) nonPubTreeRoots
  printf "NON PUBLIC TREE ROOTS: %s\n" (show nonPubTreeRoots)
  writeFile "graph2.dot" $ toDotStr nonPubTree
  system "dot -Tpdf graph2.dot -o graph2.pdf"

  shouldNotHaveCycle nonPubTree "public tree has a cycle!"

  -- let topmoduleSanitizedVars = topmoduleAnnots ^. initialEquals
  -- let hasToBeSanitized =
  --       [ v
  --       | n <- G.nodes nonPubTree
  --       , let v = toName n
  --       , Register v `elem` variables topModule && v `notElem` topmoduleSanitizedVars
  --       ]
  -- printf "non ct leaves: %s\n" $ show nonCtTreeLeaves
  -- printf "has to be public: %s\n" $ show $ HS.toList hasToBePublic
  -- unless (null hasToBeSanitized) $
  --   printf "Try sanitizing these in the top module:\n%s\n" $ T.unpack $ T.intercalate ", " hasToBeSanitized

  -- flip HM.traverseWithKey moduleSummaries $ \k qs -> do
  --   print k
  --   printSummaries qs
  --   putStrLn ""

  -- let firstNNonCTVars = take 10 $ nonCTVars topModule btm
  -- printf "first %d non ct vars:\n" (length firstNNonCTVars)
  -- traverse_ print firstNNonCTVars

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
  ((af, mm, sm), cm, FQOutAnalysisOutput {..}, moduleSummaries) <- readDebugOutput
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

prettyQualif :: FSM.TraceQualif -> String
prettyQualif = \case
  FSM.TracePublic       v  -> printf "pub(%s)" (toTVName v)
  FSM.TraceConstantTime v  -> printf "ct(%s)" (toTVName v)
  FSM.TraceUntainted    v  -> printf "untainted(%s)" (toTVName v)
  FSM.TraceSameTaint v1 v2 -> printf "eq_ct(%s, %s)" (toTVName v1) (toTVName v2)
  FSM.TraceSummary qs1 qs2 -> printf "summary(%s, %s)" (go qs1) (go qs2)
                              where go = show . fmap prettyQualif . HS.toList

printTraceDiff :: IO ()
printTraceDiff = do
  fpTrace <- readFixpointTrace
  let t = calculateSolverTraceDiff fpTrace
      qFilter = \case
        FSM.TracePublic       v -> False
        FSM.TraceConstantTime v -> True
        FSM.TraceUntainted    _ -> False
        FSM.TraceSameTaint _ _  -> False
        FSM.TraceSummary   _ _  -> False
  for_ (IM.toList t) $ \(iterNo, (cid, m)) -> do
    let m' = HM.filter (not .null) $ fmap prettyQualif . filter qFilter . HS.toList <$> m
    unless (HM.null m') $ do
      printf "iter no %d (constraint id %d)\n" iterNo cid
      for_ (HM.toList m') $ \(kv, qs) -> do
        print kv
        print qs
      putStrLn ""

fpTraceCTLoopkup :: String -> IO (Maybe Int)
fpTraceCTLoopkup arg = do
  fpTrace <- readFixpointTrace
  let lastTraceElem = snd . snd . fromJust $ IM.lookupMax fpTrace
  let btm = firstNonCT $ calculateSolverTraceDiff fpTrace
  let isCT varName =
        let v = T.unpack varName
            helper (FSM.TraceConstantTime tv) = toTVName tv == v
            helper _ = False
        in any (any helper) lastTraceElem
      getCTNo v = btmLookup btm Q_CT v <|> if isCT v then Nothing else Just 0
  return $ getCTNo $ T.pack arg

fpTraceLookupAll :: String -> IO ()
fpTraceLookupAll varName = do
  fpTrace <- readFixpointTrace
  ((af, _, summaryMap), _, _, _) <- readDebugOutput
  let helper2 qs = let qs' = HS.filter (qualifMentionsVar varName) qs
                   in if HS.null qs' then Nothing else Just qs'
      tostr = \case
        FSM.TracePublic _ -> Just "public"
        FSM.TraceConstantTime _ -> Just "ct"
        _ -> Nothing
  let ModuleSummary{..} = summaryMap HM.! (af ^. afTopModule)
  print $ threadWriteMap ^. at (T.pack varName)
  runState False $
    for_ (IM.toList fpTrace) $ \(iterNo, (cid, m)) -> do
      let m' = fmap (second (catMaybes . fmap tostr . HS.toList)) <$> HM.toList $ HM.mapMaybe helper2 m
      seenNull <- get
      unless (null m' && seenNull) $
        sendIO $ printf "%-3d %s\n" iterNo (show m')
      modify (|| null m')
  return ()

fpTraceLookup :: String -> Int -> IO FSM.SolverTraceElement
fpTraceLookup varName iterNo = do
  fpTrace <- readFixpointTrace
  let (cid, m) = fpTrace IM.! iterNo
  let helper2 qs = let qs' = HS.filter (qualifMentionsVar varName) qs
                   in if HS.null qs' then Nothing else Just qs'
  print cid
  return $ HM.mapMaybe helper2 m

fpTraceConstraints :: IO ()
fpTraceConstraints = do
  fpTrace <- readFixpointTrace
  (_, cm, _, _) <- readDebugOutput
  for_ (second ((cm IM.!) . fst) <$> IM.toList fpTrace) $ \(iterNo, md) ->
    printf "%-3d: %s\n" iterNo (FT.showFix md)

fpTraceDiff :: Int -> Int -> IO ()
fpTraceDiff n1 n2 = do
  fpTrace <- readFixpointTrace
  let m1 = snd $ fpTrace IM.! n1
  let m2 = snd $ fpTrace IM.! n2
  let fltr = \case
        FSM.TracePublic _ -> True
        FSM.TraceConstantTime _ -> True
        _ -> False
  let helper qs1 qs2 =
        let r = HS.filter fltr $ HS.difference qs1 qs2
        in if HS.null r then Nothing else Just r
  let m = HM.differenceWith helper m1 m2
  for_ (HM.toList m) $ \(k, qs) -> do
    print k
    traverse_ (putStrLn . prettyQualif) qs
    putStrLn ""

allDiffs :: IO ()
allDiffs =
  (sortOn fst . HM.toList . firstNonCT . calculateSolverTraceDiff <$> readFixpointTrace)
    >>= traverse_ print

groupSort :: Ord a => [(a, b)] -> [(a, [b])]
groupSort = fmap go . groupBy (\(a1,_) (a2, _) -> a1 == a2) . sortOn fst
  where go []           = undefined
        go ((a,b):rest) = (a, b:(snd <$> rest))

focusOnIterNo :: Int -> String -> IO ()
focusOnIterNo iterNo varNameStr = do
  fpTrace <- readFixpointTrace
  ((af, mm, sm), cm, _, _) <- readDebugOutput
  let topModuleName = af ^. afTopModule
      topModule = mm ! topModuleName
      varName = T.pack varNameStr
      deps = getVariableDependencies varName topModule sm
      varsToLookFor = varName : (fst <$> deps)
      qFilter = \case
        FSM.TracePublic       v -> True
        FSM.TraceConstantTime v -> True
        FSM.TraceUntainted    _ -> False
        FSM.TraceSameTaint _ _  -> False
        FSM.TraceSummary   _ _  -> False
      fltr = HS.filter $ \q -> qFilter q && any (\v -> qualifMentionsVar (T.unpack v) q) varsToLookFor
      swap (a,b) = (b,a)

  putStrLn (T.unpack varName)
  for_ (fmap (second sort) $ groupSort $ swap <$> deps) print
  putStrLn ""

  let fpList = [ (i, cid, m')
               | a@(i, (cid, m)) <- IM.toList fpTrace
               , abs (iterNo - i) < 2
               , let m' = HM.filter (not . HS.null) $ HM.map fltr m
               , not (HM.null m')
               ]
  for_ fpList $ \(i, cid, m) -> do
    printf "iter no %d\nconstraint %d: %s\n" i cid (FT.showFix $ cm IM.! cid)
    HM.traverseWithKey (\k qs -> print k >> print (prettyQualif <$> sort (HS.toList qs))) m
    putStrLn "\n"