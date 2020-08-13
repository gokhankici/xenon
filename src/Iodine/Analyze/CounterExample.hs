{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

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
import           Control.Lens
import           Control.Monad
import           Data.Bifunctor
import           Data.Foldable
import qualified Data.Graph.Inductive as G
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

_tst :: IO ()
_tst = do
  (af, moduleMap, summaryMap, finfo, enableAbductionLoop) <- readGCEInput
  generateCounterExampleGraphs af moduleMap summaryMap finfo enableAbductionLoop

--------------------------------------------------------------------------------
generateCounterExampleGraphs
  :: AnnotationFile -> ModuleMap -> SummaryMap -> FInfo -> Bool -> IO ()
--------------------------------------------------------------------------------
generateCounterExampleGraphs af moduleMap summaryMap finfo enableAbductionLoop = do
  writeGCEInput (af, moduleMap, summaryMap, finfo, enableAbductionLoop)
  let cm = toConstraintTypes finfo
  fpTrace <- readFixpointTrace
  let fpTraceDiff          = firstNonCT $ calculateSolverTraceDiff fpTrace
      topmoduleName        = af ^. afTopModule
      mAnnots              = toModuleAnnotations topmoduleName af
      topmoduleAnnots      = mAnnots ^. moduleAnnotations
      ieVars               = topmoduleAnnots ^. initialEquals
      aeVars               = topmoduleAnnots ^. alwaysEquals
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

  let createDepTreeHelper = createDepTree varNames (varDepMap HM.!) toNode toName isHorn

  -- ---------------------------------------------------------------------------
  -- 1. data-flow graph part
  -- ---------------------------------------------------------------------------

  let getHornCTNo = btmLookupF topModuleIdCheck fpTraceDiff Q_CT

  let nonCtTree = createDepTreeHelper getHornCTNo

  -- print nonCtTree >> exitFailure

  let ns = G.labNodes nonCtTree
      nonPosNodes = filter ((<= 0) . snd) ns
      in unless (null nonPosNodes) $ do
           for_ nonPosNodes print
           error "nonCtTree labels must be positive"

  -- these are the root causes of the verification failure
  let nonCtTreeRoots = fmap (first toName) <$> getRootLikeNodes nonCtTree

  putStrLn "### NON CT TREE ROOTS #############################################"
  for_ nonCtTreeRoots (traverse_ print) >> putStrLn ""

  let minCtTreeRoots :: [(Id, Int)] =
        let getMin = minimum . fmap snd
            clustersWithMinIterNos = (\l -> (l, getMin l)) <$> nonCtTreeRoots
            minClusterIterNo = getMin clustersWithMinIterNos
        in nub' id
           [ l
           | (c, i) <- clustersWithMinIterNos
           , i == minClusterIterNo
           , l <- c
           ]

  printf "Min roots: %s\n\n" $ show $ fst <$> minCtTreeRoots

  when generateGraphPDF $ do
    writeFile "nonCtTree.dot" $ toCtTreeDotStr nonCtTree
    callDot "nonCtTree.dot" "nonCtTree.pdf"

  -- ---------------------------------------------------------------------------
  -- 2. control-flow graph
  -- ---------------------------------------------------------------------------

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

  -- first create the cfg for every variable
  let nonPubTree0 = createDepTreeHelper getHornPubNo

  -- then pick the ones that are the implicit dependencies of the causes to be
  -- the leaves
  let nonPubTreeNodes0 = IS.fromList $ G.nodes nonPubTree0
  let hasToBePublic leaf = nub' id
        [ childName
        | (childName, _) <- getDeps leaf
        , toNode childName `IS.member` nonPubTreeNodes0
        ]
  let nonPubTreeLeaves = nub' id $ minCtTreeRoots >>= hasToBePublic . fst

  -- keep the implicit variables that are the dependencies of the causes
  let nonPubTree :: TstG =
        let revG = G.grev nonPubTree0
            go ntk l = ntk <> IS.fromList (G.reachable (toNode l) revG)
            nodesToKeep  = foldl' go IS.empty nonPubTreeLeaves
        in G.grev $ G.nfilter (`IS.member` nodesToKeep) revG

  putStrLn "### NON PUBLIC TREE LEAVES ########################################"
  for_ nonPubTreeLeaves (putStrLn . T.unpack) >> putStrLn ""

  when generateGraphPDF $ do
    writeFile "nonPubTree.dot" $ toDotStr (invVariableDependencyNodeMap IM.!)
      (\i ->
        if iterToConstraintType i == Just Init
        then " (Init #" <> show i <> ")"
        else " (" <> show i <> ")"
      )
      edgeStyle
      nonPubTree0
    callDot "nonPubTree.dot" "nonPubTree.pdf"

  -- ---------------------------------------------------------------------------
  -- 3. MILP
  -- ---------------------------------------------------------------------------

  let ilpGraph       = nonPubTree
      mustBePublic   = toNode <$> nonPubTreeLeaves
      cannotBeMarked =
        let fltr v = T.isPrefixOf inlinePrefix v &&
                     not (null $ getDeps v)
            extraUnmarked =
              if doNotMarkSubmoduleVariables
              then SQ.filter fltr varNames
              else mempty
        in toList $ fmap toNode $
           (toSequence $ topmoduleAnnots ^. cannotMarks) <> extraUnmarked
      loops = let (pubSCC, _) = sccGraph ilpGraph
              in [ IS.toList l
                 | sccN <- G.nodes pubSCC -- sccN is a components
                 , null $ G.pre pubSCC sccN -- and it is a root
                 , let l = fromJust (G.lab pubSCC sccN)
                 , IS.size l > 1
                 ]
  for_ loops $ \l -> printf "loop: %s\n" (show $ toName <$> l)
  ilpResult <- if enableAbductionLoop
               then runILPLoop mustBePublic cannotBeMarked loops ilpGraph toName
               else runILP mustBePublic cannotBeMarked loops ilpGraph
  case ilpResult of
    Left errMsg -> putStrLn errMsg
    Right (cannotMark', pubNodes, markedNodes) -> do
      let sep = putStrLn $ replicate 80 '-'
          prints = traverse_ putStrLn . sort . fmap (T.unpack . toName)
      sep
      if null markedNodes
        then do putStrLn "\n\nHuh, there are no nodes to mark ..."
                putStrLn "Maybe you should mark these non-constant-time leaf variables as public:"
                print $ fst <$> minCtTreeRoots
        else do putStrLn "marked nodes:" >> putStrLn "---" >> prints markedNodes
      sep
      let initEqCandidates :: [Int] =
            filter
            (\n -> let v = toName n
                   in isReg v && v `notElem` ieVars && v `notElem` aeVars)
            pubNodes
      putStrLn "initial_eq candidates:" >> putStrLn "---" >> prints initEqCandidates
      sep
      putStrLn "cannotMark':" >> putStrLn "---" >> print (toName <$> cannotMark')
      sep

  when generateGraphPDF $ do
    writeFile "nonPubTreeSCC.dot" $
      toDotStr (\n -> toName n <> " : " <> T.pack (show n)) (const "") edgeStyle ilpGraph
    callDot "nonPubTreeSCC.dot" "nonPubTreeSCC.pdf"

-- | label of the parent node is greater than its children
createDepTree :: L Id                            -- ^ variables
              -> (Id -> [(Id, VarDepEdgeType)])  -- ^ get dependencies
              -> (Id -> Int)                     -- ^ variable name to node number
              -> (Int -> Id)                     -- ^ node number to variable name
              -> (Id -> Bool)                    -- ^ is horn variable
              -> (Id -> Maybe Int)               -- ^ get lost iteration no of horn variables
              -> G.Gr Int VarDepEdgeType         -- ^ dependency graph
createDepTree vars getDeps toNode toName isHorn getHornLostIterNo =
  G.mkGraph nodes edges'
  where
    nodes =
      fmap (\v -> (toNode v, getActualIterNo v)) $
      HS.toList $
      foldl'
      (\acc (p,c,_) -> HS.insert p $ HS.insert c acc)
      HS.empty
      edges

    edges' = (_1 %~ toNode) . (_2 %~ toNode) <$> edges

    edges = do
      child <- toList vars
      (parent, edgeType) <- getDeps child
      let parentIterNo = getActualIterNo parent
          childIterNo = getActualIterNo child
      if 0 <= parentIterNo && parentIterNo <= childIterNo
        then return (parent, child, edgeType)
        else []

    getActualIterNo v =
      deepseq actualIterNoMap $
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

    actualIterNoMap = actualIterNoMapHelper mempty vdg (mkSCC vdg)

    actualIterNoMapHelper :: HM.HashMap Id Int
                          -> G.Gr () VarDepEdgeType
                          -> G.Gr IS.IntSet VarDepEdgeType
                          -> HM.HashMap Id Int
    -- actualIterNoMapHelper ainm _ _
    --   | DT.trace ("actualIterNoMapHelper " <> show [show $ length $ HM.toList ainm]) False = undefined
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
    -- actualIterNoLoop (_,   v SQ.:<| _ ) | DT.trace ("actualIterNoLoop " <> T.unpack v) False = undefined
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
