{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Iodine.Analyze.CounterExample
  ( readFixpointTrace
  , toTVName
  , firstNonCT
  , ConstraintTypes
  , toConstraintTypes
  , QualType(..)
  , btmLookup
  , btmLookupF
  , calculateSolverTraceDiff
  , generateCounterExampleGraphs
  )
where

import           Iodine.Analyze.DependencyGraph
import           Iodine.Analyze.ILP
import           Iodine.Analyze.ModuleSummary
import           Iodine.ConstantConfig
import           Iodine.Language.Annotation
import           Iodine.Language.IR as IR
import           Iodine.Transform.Fixpoint.Common (FInfo, HornClauseId, hcType)
import           Iodine.Transform.Horn
import           Iodine.Transform.Inline (inlinePrefix)
import           Iodine.Transform.VCGen2 (computeHornVariables)
import           Iodine.Types
import           Iodine.Utils

import qualified Language.Fixpoint.Solver.Monad as FSM
import qualified Language.Fixpoint.Types       as FT

import           Control.Applicative
import           Control.DeepSeq (deepseq)
import           Control.Lens hiding ((<.>))
import           Control.Monad
import           Data.Bifunctor
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive.Query.SP as GSP
import           Data.Hashable
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import           Data.List
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import qualified Debug.Trace as DT
import           Data.Maybe
import           GHC.Generics hiding ( moduleName )
-- import           System.Exit (exitFailure)
import           System.Process
import           Text.Printf
import           System.FilePath

type ConstraintTypes = IM.IntMap HornClauseId
type ModuleMap = HM.HashMap Id (Module Int)
type TstG = G.Gr Int VarDepEdgeType

-- Variable Name -> KVar Id -> Qualifier Type -> Index
type BetterTraceMap = HM.HashMap T.Text (IM.IntMap (HM.HashMap QualType Int))

data QualType = Q_CT | Q_PUB deriving (Show, Eq, Generic)
instance Hashable QualType

toConstraintTypes :: FInfo -> ConstraintTypes
toConstraintTypes =
  IM.fromList . fmap (bimap fromIntegral FT.sinfo) . HM.toList . FT.cm

readFixpointTrace :: IO FSM.SolverTrace
readFixpointTrace = FSM.readSolverTrace "fixpoint-trace.json"

toTVName :: FSM.TraceVar -> String
toTVName (FSM.TraceVar _ tv _) = tv

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

btmLookup :: BetterTraceMap -> QualType -> Id -> Maybe Int
btmLookup = btmLookupF (const True)

btmLookupF :: (Int -> Bool) -> BetterTraceMap -> QualType -> Id -> Maybe Int
btmLookupF kvarIdCheck btm qt varName = do
  kvs <- btm ^. at varName
  case filter (kvarIdCheck . fst) $ IM.toList kvs of
    [(_, m)] -> m ^. at qt
    qsList ->
      case (snd <$> qsList) >>= toList . HM.lookup qt of
        []   -> Nothing
        i:is -> DT.trace (printf "Multiple iterNos for %s: %s" varName (show $ i:is)) $
                Just $ foldl' min i is

type GCEInput = (AnnotationFile, ModuleMap, SummaryMap, FInfo, Bool)

writeGCEInput :: GCEInput -> IO ()
writeGCEInput (af, moduleMap, summaryMap, _, enableAbductionLoop) =
  writeFile "gce-input" $ show (af, moduleMap, summaryMap, enableAbductionLoop)

readGCEInput :: IO GCEInput
readGCEInput = do
  (af, moduleMap, summaryMap, enableAbductionLoop) <- read <$> readFile "gce-input"
  return (af, moduleMap, summaryMap, mempty, enableAbductionLoop)

_tst :: Bool -> IO ()
_tst wpl = do
  (af, moduleMap, summaryMap, finfo, enableAbductionLoop) <- readGCEInput
  generateCounterExampleGraphsH af moduleMap summaryMap finfo enableAbductionLoop wpl



--------------------------------------------------------------------------------
generateCounterExampleGraphs
  :: AnnotationFile -> ModuleMap -> SummaryMap -> FInfo -> Bool -> IO ()
--------------------------------------------------------------------------------
generateCounterExampleGraphs af moduleMap summaryMap finfo enableAbductionLoop = do
  writeGCEInput (af, moduleMap, summaryMap, finfo, enableAbductionLoop)
  generateCounterExampleGraphsH af moduleMap summaryMap finfo enableAbductionLoop False

generateCounterExampleGraphsH
  :: AnnotationFile -> ModuleMap -> SummaryMap -> FInfo -> Bool -> Bool -> IO ()
generateCounterExampleGraphsH af moduleMap summaryMap finfo enableAbductionLoop withPublicLoop = do
  let cm = toConstraintTypes finfo
  fpTrace <- readFixpointTrace
  let fpTraceDiff          = firstNonCT $ calculateSolverTraceDiff fpTrace
      topmoduleName        = af ^. afTopModule
      mAnnots              = toModuleAnnotations topmoduleName af
      topmoduleAnnots      = mAnnots ^. moduleAnnotations
      srcs                 = topmoduleAnnots ^. sources
      topModule            = fromJust $ moduleMap ^. at topmoduleName
      topModuleIdCheck     = (`elem` (getData <$> alwaysBlocks topModule))
      ms@ModuleSummary{..} = fromJust $ summaryMap ^. at topmoduleName
      toNode               = (variableDependencyNodeMap HM.!)
      toName               = (invVariableDependencyNodeMap IM.!)
      getDeps v            = getVariableDependencies v topModule summaryMap
      clks                 = mAnnots ^. clocks
      notAClock            = (`notElem` clks)
      vars                 = SQ.filter (notAClock . variableName) $ variables topModule
      varNames             = variableName <$> vars
      varDepMap            = foldl' (\acc v -> HM.insert v (getDeps v) acc) mempty varNames
      isReg v              = Register v `elem` vars

  let iterToConstraintType iterNo = do
        constraintNo   <- fst <$> fpTrace ^. at iterNo
        constraintType <- cm ^. at constraintNo
        return $ hcType constraintType

  let hornVariables = computeHornVariables topModule ms mAnnots
      isHorn        = (`HS.member` hornVariables)

  let toCtTreeDotStr =
        toDotStr (invVariableDependencyNodeMap IM.!) (printf " #%d") edgeStyle

  let createDepTreeHelper =
        let lkpDeps v = case varDepMap ^. at v of
                          Nothing -> error $ printf "%s not in varDepMap" v
                          Just ds -> ds
        in createDepTree varNames lkpDeps toNode toName isHorn

  -- ---------------------------------------------------------------------------
  -- 1. data-flow graph part
  -- ---------------------------------------------------------------------------

  let getHornCTNo = btmLookupF topModuleIdCheck fpTraceDiff Q_CT

  let nonCtTree =
        let g = createDepTreeHelper getHornCTNo
            snks = topmoduleAnnots ^. sinks
            revG = G.grev g
            nodesToKeep =
              IS.toList $
              foldl' (\acc s ->
                let n = toNode s
                    ns = G.reachable n revG
                in IS.fromList ns <> acc
              ) IS.empty snks
        in G.subgraph nodesToKeep g

  -- sanity check
  do let ns = G.labNodes nonCtTree
         nonPosNodes = filter ((<= 0) . snd) ns
     unless (null nonPosNodes) $ do
       for_ nonPosNodes print
       error "nonCtTree labels must be positive"

  minCtTreeRoots <- computeMinCTRoots nonCtTree toName

  unless (nodeSize nonCtTree > maxFeasibleNodeCount) $ do
    printGraph "nonCtTree" $ toCtTreeDotStr nonCtTree

  let lastTraceElementPubs =
        let (_maxIterNo, (_constraintId, qualMap)) = IM.findMax fpTrace
            mkKVar n = T.pack $ "inv" <> show n
            kvNames = (mkKVar $ getThreadId topModule) :
                      case alwaysBlocks topModule of
                        SQ.Empty          -> []
                        a SQ.:<| SQ.Empty -> [mkKVar $ getThreadId a]
                        _                 -> error "unreachable"
        in HS.fromList
           [ v
           | (kv, qs) <- HM.toList qualMap
           , kv `elem` kvNames
           , q <- toList qs
           , v <- case q of
                    FSM.TracePublic tv -> [T.pack $ toTVName tv]
                    _ -> []
           ]
  let getHornPubNo v =
        btmLookupF topModuleIdCheck fpTraceDiff Q_PUB v <|>
        if v `elem` lastTraceElementPubs then Nothing else Just 0

  let (ilpCostMap, varDepGraph0) =
        computeILPCosts
        topModule moduleMap summaryMap
        toNode
        ((+ 1) $ fst $ IM.findMax invVariableDependencyNodeMap)
        srcs
      varDepGraph =
        G.nfilter (\n -> IM.member n ilpCostMap) varDepGraph0
  let ilpCosts n = fromMaybe 0 $ ilpCostMap ^. at n

  secondAndThirdPhase PhaseData{ nonPublicNodes = mempty
                               , ..
                               }

type IndexLookup = Id -> Maybe Int

data PhaseData = PhaseData
     { nonCtTree            :: TstG
     , minCtTreeRoots       :: [(Id, Int)] -- ^ variable name & iteration number
     , createDepTreeHelper  :: IndexLookup -> TstG
     , enableAbductionLoop  :: Bool
     , getDeps              :: Id -> [(Id, VarDepEdgeType)]
     , getHornPubNo         :: IndexLookup
     , ilpCosts             :: Int -> Integer
     , isReg                :: Id -> Bool
     , iterToConstraintType :: Int -> Maybe HornType
     , moduleMap            :: ModuleMap
     , ms                   :: ModuleSummary
     , toName               :: Int -> Id
     , toNode               :: Id -> Int
     , topModule            :: Module Int
     , topmoduleAnnots      :: Annotations
     , varNames             :: L Id
     , varDepGraph          :: VarDepGraph
     , nonPublicNodes       :: IS.IntSet
     , isHorn               :: Id -> Bool
     , withPublicLoop       :: Bool
     }

-- -----------------------------------------------------------------------------
secondAndThirdPhase :: PhaseData -> IO ()
-- -----------------------------------------------------------------------------
secondAndThirdPhase PhaseData{..} | not enableAbductionLoop = return ()

secondAndThirdPhase PhaseData{..} | withPublicLoop || null minCtTreeRoots = do
  let invVarDepGraph = G.grev varDepGraph
      srcs = topmoduleAnnots ^. sources
      registerDependencies v =
        let ds = G.reachable (toNode v) invVarDepGraph
        in filter isReg $ toName <$> ds
      sourceDeps v =
        let ds = G.reachable (toNode v) invVarDepGraph
        in filter (`elem` srcs) $ toName <$> ds
      printInfo v = do
        let n = toNode v
            skip = not (n `IS.member` nonPublicNodes) || inlinePrefix `T.isPrefixOf` v
        unless skip $ do
          printf " - %s (%s%s)\n" v
            (if isReg v  then " R " else " W " :: String)
            (if isHorn v then " H " else " . " :: String)
          printf "   - register dependencies: %s\n" (show $ registerDependencies v)
          printf "   - source dependencies:   %s\n" (show $ sourceDeps v)
          putStrLn ""

  putStrLn "-------------------------------------------------------------------"
  putStrLn "public nodes"
  putStrLn "-------------------------------------------------------------------"
  for_ varNames printInfo

  let snks = topmoduleAnnots ^. sinks

  let mkILPInput ilpGraph =
        let cannotMarkFilter v = T.isPrefixOf inlinePrefix v && not (null $ getDeps v)
            cannotBeMarked =
              let extraUnmarked1 =
                    if doNotMarkSubmoduleVariables
                    then SQ.filter cannotMarkFilter varNames
                    else mempty
                  extraUnmarked2 = toSequence snks
              in toList $ fmap toNode $
                 (toSequence $ topmoduleAnnots ^. cannotMarks)
                 <> extraUnmarked1
                 <> extraUnmarked2
            loops = let (pubSCC, _) = sccGraph ilpGraph
                    in [ IS.toList l
                       | sccN <- G.nodes pubSCC -- sccN is a components
                       , null $ G.pre pubSCC sccN -- and it is a root
                       , let l = fromJust (G.lab pubSCC sccN)
                       , IS.size l > 1
                       ]
        in (cannotBeMarked, loops)

  putStrLn "-------------------------------------------------------------------"
  putStrLn "\n\n\n"
  putStrLn "minCtTreeRoots is empty ..."
  putStrLn "enter a variable name to see how to make it public:"

  mui <- fmap T.words <$> getUserInput

  case mui of
    Just [v] | v `elem` varNames -> do
      printInfo v
      let ilpGraph = createDepTreeHelper getHornPubNo

      putStrLn "### NON PUBLIC TREE REGISTERS #####################################"
      for_ (G.nodes ilpGraph) $ \n -> do
        let ilp_v = toName n
            isIE = ilp_v `elem` topmoduleAnnots ^. initialEquals
            isAE = ilp_v `elem` topmoduleAnnots ^. alwaysEquals
            mkFlag b s = if b then " " <> s else "" :: String
        when (isReg ilp_v && not isAE) $
          printf " - %s%s\n" ilp_v (mkFlag isIE "(I)")
      putStrLn "\n"

      let (cannotBeMarked, loops) = mkILPInput ilpGraph
      result <- runILPLoop [toNode v] cannotBeMarked loops ilpGraph ilpCosts toName
      case result of
        Left errMsg -> putStrLn errMsg
        _ -> return ()
      secondAndThirdPhase PhaseData{..}
    _ -> putStrLn "invalid/empty user input"

secondAndThirdPhase PhaseData{..} = do
  let ModuleSummary{..} = ms
      snks   = topmoduleAnnots ^. sinks
      ieVars = topmoduleAnnots ^. initialEquals
      aeVars = topmoduleAnnots ^. alwaysEquals

  -- ---------------------------------------------------------------------------
  -- 2. control-flow graph
  -- ---------------------------------------------------------------------------

  -- first create the cfg for every variable
  let nonPubTree0 = createDepTreeHelper getHornPubNo

  -- then pick the ones that are the implicit dependencies of the causes to be
  -- the leaves
  let nonPubTreeNodes0 = IS.fromList $ G.nodes nonPubTree0
  let hasToBePublic leaf = nub' id
        [ childName
        | (childName, edgeType) <- getDeps leaf
        , edgeType == Implicit
        , toNode childName `IS.member` nonPubTreeNodes0
        ]
  let nonPubTreeLeaves = nub' id $ minCtTreeRoots >>= hasToBePublic . fst

  -- keep the implicit variables that are the dependencies of the causes
  let nonPubTree :: TstG =
        let revG = G.grev nonPubTree0
            go ntk l = ntk <> IS.fromList (G.reachable (toNode l) revG)
            nodesToKeep  = foldl' go IS.empty nonPubTreeLeaves
        in G.grev $ G.nfilter (`IS.member` nodesToKeep) revG

  putStrLn "### NON PUBLIC TREE REGISTERS #####################################"
  for_ (G.nodes nonPubTree) $ \n -> do
    let v = toName n
        isIE = v `elem` topmoduleAnnots ^. initialEquals
        isAE = v `elem` topmoduleAnnots ^. alwaysEquals
        mkFlag b s = if b then " " <> s else "" :: String
    when (isReg v && not isAE) $
      printf " - %s%s\n" v (mkFlag isIE "(I)")
  putStrLn "\n"

  putStrLn "### NON PUBLIC TREE LEAVES ########################################"
  for_ nonPubTreeLeaves (putStrLn . T.unpack) >> putStrLn ""

  unless (nodeSize nonPubTree > maxFeasibleNodeCount) $
    let dotStr = toDotStr (invVariableDependencyNodeMap IM.!)
                 (\i ->
                   if iterToConstraintType i == Just Init
                   then " (Init #" <> show i <> ")"
                   else " (" <> show i <> ")"
                 )
                 edgeStyle
                 nonPubTree
    in printGraph "nonPubTree" dotStr

  -- ---------------------------------------------------------------------------
  -- 3. MILP
  -- ---------------------------------------------------------------------------

  putStrLn "### ILP PHASE #####################################################"

  let ilpGraph       = nonPubTree
      mustBePublic   = toNode <$> nonPubTreeLeaves
      cannotMarkFilter v = T.isPrefixOf inlinePrefix v && not (null $ getDeps v)
      cannotBeMarked =
        let extraUnmarked1 =
              if doNotMarkSubmoduleVariables
              then SQ.filter cannotMarkFilter varNames
              else mempty
            extraUnmarked2 = toSequence snks
        in toList $ fmap toNode $
           (toSequence $ topmoduleAnnots ^. cannotMarks)
           <> extraUnmarked1
           <> extraUnmarked2
      loops = let (pubSCC, _) = sccGraph ilpGraph
              in [ IS.toList l
                 | sccN <- G.nodes pubSCC -- sccN is a components
                 , null $ G.pre pubSCC sccN -- and it is a root
                 , let l = fromJust (G.lab pubSCC sccN)
                 , IS.size l > 1
                 ]

  ilpResult <- if enableAbductionLoop
               then runILPLoop mustBePublic cannotBeMarked loops ilpGraph ilpCosts toName
               else runILP     mustBePublic cannotBeMarked loops ilpGraph ilpCosts

  case ilpResult of

    Left errMsg -> do

      putStrLn ""
      putStrLn $ "ilp solver did not succeed: " <> errMsg
      putStrLn ""

      -- printf "must be public:   %s\n\n" $ show $ toName <$> mustBePublic
      -- printf "cannot be marked: %s\n\n" $ show $ toName <$> cannotBeMarked

      let nodesToRemove = toNode . fst <$> minCtTreeRoots
      let nonCtTree' = G.nfilter (`notElem` nodesToRemove) nonCtTree
      minCtTreeRoots' <- computeMinCTRoots nonCtTree' toName

      secondAndThirdPhase PhaseData { nonCtTree      = nonCtTree'
                                    , minCtTreeRoots = minCtTreeRoots'
                                    , nonPublicNodes    =
                                        if IS.null nonPublicNodes
                                        then nonPublicNodes
                                             <> (IS.fromList $ G.nodes nonPubTree0)
                                        else nonPublicNodes
                                    , ..
                                    }

    Right (cannotMark', pubNodes, markedNodes) -> do

      let sep = putStrLn $ replicate 80 '-'
          prints = traverse_ (printf "- %s\n") . sort . fmap (T.unpack . toName)
      sep
      if null markedNodes
        then do putStrLn "\n\nHuh, there are no nodes to mark ..."
                putStrLn "Maybe you should mark these non-constant-time leaf variables as public:"
                print $ fst <$> minCtTreeRoots
        else return () -- do putStrLn "marked nodes:" >> putStrLn "---" >> prints markedNodes
      sep
      let initEqCandidates :: [Int] =
            filter
            (\n -> let v = toName n
                   in isReg v && v `notElem` ieVars && v `notElem` aeVars)
            (nub' id $ pubNodes <> markedNodes)
      putStrLn "initial_eq candidates:" >> putStrLn "---" >> prints initEqCandidates
      sep
      putStrLn "cannotMark':" >> putStrLn "---" >> print (filter (not . cannotMarkFilter) $ toName <$> cannotMark')
      sep

      unless (nodeSize ilpGraph > maxFeasibleNodeCount) $
        let dotStr =
              toDotStr (\n -> toName n <> " : " <> T.pack (show n)) (const "") edgeStyle ilpGraph
        in printGraph "nonPubTreeSCC" dotStr


-- -----------------------------------------------------------------------------
computeMinCTRoots :: TstG -> (Int -> Id) -> IO [(Id, Int)]
-- -----------------------------------------------------------------------------
computeMinCTRoots nonCtTree toName = do
  -- these are the root causes of the verification failure
  let nonCtTreeSCCRoots = fmap (first toName) <$> getRootLikeNodes nonCtTree

  putStrLn "### NON CT TREE ROOTS #############################################"
  for_ (zip [1..] (concat nonCtTreeSCCRoots)) print >> putStrLn ""

  let minCtTreeRoots :: [(Id, Int)] =
        let getMin = minimum . fmap snd
            clustersWithMinIterNos = (\l -> (l, getMin l)) <$> nonCtTreeSCCRoots
            minClusterIterNo = getMin clustersWithMinIterNos
        in nub' id
           [ l
           | (c, i) <- clustersWithMinIterNos
           , i == minClusterIterNo
           , l <- c
           ]

  printf "Min roots (%d): %s\n\n"
    (length minCtTreeRoots) (show $ fst <$> minCtTreeRoots)

  return minCtTreeRoots


-- -----------------------------------------------------------------------------
computeILPCosts :: Module Int
                -> ModuleMap
                -> SummaryMap
                -> (Id -> Int)
                -> Int
                -> Ids
                -> (IM.IntMap Integer, G.Gr () VarDepEdgeType)
-- -----------------------------------------------------------------------------
computeILPCosts topModule moduleMap summaryMap toNode rootNode srcs =
  (foldl' addCost mempty paths, fixedG)
  where
    distToCost d = 10 * (2 ^ d)

    addCost _ (G.LP []) = error "unreachable"
    addCost m (G.LP ((n, d):_)) =
      if n /= rootNode
      then IM.insert n (distToCost d) m
      else m

    paths = GSP.spTree rootNode fixedG_edgeCosts

    fixedG_edgeCosts = G.emap (const 1) fixedG_withEdges
    fixedG_withEdges = foldl' (flip G.insEdge) fixedG_withRoot extraNodes
    extraNodes       = (\s -> (rootNode, toNode s, Explicit False)) <$> toList srcs
    fixedG_withRoot  = G.insNode (rootNode, ()) fixedG

    fixedG = varDepGraphWithInstanceEdges topModule moduleMap summaryMap

-- -----------------------------------------------------------------------------
-- | label of the parent node is greater than its children
createDepTree :: L Id                            -- ^ variables
              -> (Id -> [(Id, VarDepEdgeType)])  -- ^ get dependencies
              -> (Id -> Int)                     -- ^ variable name to node number
              -> (Int -> Id)                     -- ^ node number to variable name
              -> (Id -> Bool)                    -- ^ is horn variable
              -> (Id -> Maybe Int)               -- ^ get lost iteration no of horn variables
              -> G.Gr Int VarDepEdgeType         -- ^ dependency graph
-- -----------------------------------------------------------------------------
createDepTree vars getDeps toNode toName isHorn getHornLostIterNo =
  G.mkGraph nodes edges
  where
    nodes =
      [ (toNode v, i)
      | v <- toList vars
      , let i = getActualIterNo v
      , i >= 0
      ]

    edges = do
      child <- toList vars
      (parent, edgeType) <- getDeps child
      let parentIterNo = getActualIterNo parent
          childIterNo = getActualIterNo child
      if 0 <= parentIterNo && parentIterNo <= childIterNo
        then return (toNode parent, toNode child, edgeType)
        else []

    getActualIterNo v =
      case actualIterNoMap ^. at v of
        Nothing -> error $ printf "could not find %s in actualIterNoMap" v
        Just i  -> i

    getSCCNodes sccG sccN =
      fmap toName $
      IS.toList $ fromJust $
      G.lab sccG sccN

    vdg = G.mkGraph ns es
      where
        vs = toList vars
        ns = (, ()) . toNode <$> vs
        es = do
          c <- vs
          (p, t) <- getDeps c
          return (toNode p, toNode c, t)

    mkSCC = fst . sccGraph

    actualIterNoMap =
      let m = actualIterNoMapHelper mempty vdg (mkSCC vdg)
          -- m = DT.trace (unlines ("actualIterNoMap:" : (show <$> HM.toList _m))) _m
      in deepseq m m

    actualIterNoMapHelper :: HM.HashMap Id Int
                          -> G.Gr () VarDepEdgeType
                          -> G.Gr IS.IntSet VarDepEdgeType
                          -> HM.HashMap Id Int
    -- actualIterNoMapHelper ainm _ _
    --   | DT.trace ("actualIterNoMapHelper " <> prntMap ainm) False = undefined
    actualIterNoMapHelper ainm g sccG = foldl' (\acc sccN ->
      let (hvs, nhvs) = partition isHorn (getSCCNodes sccG sccN)
          ws          = if null hvs then nhvs else hvs
          acc'        = fst $ actualIterNoLoop (acc, SQ.fromList ws)
          missingVars = toNode <$> filter (not . (`HM.member` acc')) nhvs
          g'          = G.subgraph missingVars g
          sccG'       = mkSCC g'
      in if | null missingVars -> acc'
            | otherwise -> actualIterNoMapHelper acc' g' sccG'
      ) ainm (G.topsort sccG)

    actualIterNoLoop (lkp, m@SQ.Empty   ) = (lkp, m)
    -- actualIterNoLoop (lkp, v SQ.:<| _ )
    --   | DT.trace (unlines ["actualIterNoLoop " <> T.unpack v, prntMap lkp]) False = undefined
    actualIterNoLoop (lkp, v SQ.:<| vs) =
      case actualIterNoLoopHelper lkp v of
        Nothing -> actualIterNoLoop (lkp, vs)
        Just i  -> let lkp' = HM.insert v i lkp
                   in deepseq lkp' $ actualIterNoLoop (lkp', vs)

    alwaysAvailable = -1

    -- return a Just if we know the actual iteration count
    -- Nothing   := we do not know the actual iteration count
    -- Just (-1) := always available
    -- Just 0    := always missing
    -- Just i    := available at (i-1) but lost at i
    actualIterNoLoopHelper :: HM.HashMap Id Int -> Id -> Maybe Int
    actualIterNoLoopHelper lkp v =
      if isHorn v
      -- if v is a horn variable, and getHornIterNo returns nothing, use -1 as
      -- the iteration count
      then case getHornLostIterNo v of
             Nothing -> Just alwaysAvailable
             Just i  -> Just i
      else case actualIterNoLoopHelper lkp . fst <$> getDeps v of
             -- all variables without dependencies should be a horn variable,
             -- unless they are constant expressions
             [] -> Just alwaysAvailable
             -- if we know the count of every dependency ...
             is | all isJust is ->
               case filter (/= alwaysAvailable) $ fromJust <$> is of
                 -- if there is no non-negative dependency, use -1
                 [] -> Just alwaysAvailable
                 is2 -> Just $ minimum is2
             -- if there is a dependency with missing iter count ...
             _ -> Nothing


printGraph :: String -> String -> IO ()
printGraph _ _ | not generateGraphPDF = return ()
printGraph name dotStr = do
  writeFile dotFile dotStr
  callDot dotFile pdfFile
  where
    dotFile = name <.> "dot"
    pdfFile = name <.> "pdf"

    callDot :: String -> String -> IO ()
    callDot i o = do
      system $ printf "dot -Tpdf -Gmargin=0 '%s' -o '%s'" i o
      return ()

getRootLikeNodes :: Eq b => G.Gr a b -> [[G.LNode a]]
getRootLikeNodes = getLLNHelper G.indeg

getLLNHelper :: Eq b => (forall c d. G.Gr c d -> Int -> Int) -> G.Gr a b -> [[G.LNode a]]
getLLNHelper f g = fmap (\n -> (n, fromJust $ G.lab g n)) <$> ls
 where
  (sccG, _) = sccGraph g
  go acc (sccN, sccNs) = if f sccG sccN == 0 then IS.toList sccNs : acc else acc
  ls = foldl' go mempty (G.labNodes sccG)

edgeStyle :: VarDepEdgeType -> String
edgeStyle Implicit     = "dashed"
edgeStyle (Explicit _) = "solid"

nodeSize :: G.Graph gr => gr a b -> Int
nodeSize = length . G.nodes