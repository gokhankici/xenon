{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


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

import           Iodine.Analyze.ModuleSummary
import           Iodine.Analyze.DependencyGraph
import           Iodine.Language.Annotation
import           Iodine.Language.IR            as IR
import           Iodine.Transform.Horn
import           Iodine.Types
import           Iodine.Utils
import           Iodine.Transform.Fixpoint.Common
                                                ( FInfo
                                                , HornClauseId
                                                , hcType
                                                )

import           Control.Lens
import           Control.Applicative
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
import qualified Data.Text                     as T
import qualified Language.Fixpoint.Solver.Monad
                                               as FSM
import           Text.Printf
import           GHC.Generics            hiding ( moduleName )
import qualified Debug.Trace                   as DT
import           System.Process
import qualified Language.Fixpoint.Types       as FT

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

--------------------------------------------------------------------------------
generateCounterExampleGraphs
  :: AnnotationFile -> ModuleMap -> SummaryMap -> FInfo -> IO ()
--------------------------------------------------------------------------------
generateCounterExampleGraphs af moduleMap summaryMap finfo = do
  let cm = toConstraintTypes finfo
  fpTrace <- readFixpointTrace
  let lastTraceElem = snd . snd . fromJust $ IM.lookupMax fpTrace
  let btm           = firstNonCT $ calculateSolverTraceDiff fpTrace
  let
    topmoduleName      = af ^. afTopModule
    topmoduleAnnots = toModuleAnnotations topmoduleName af ^. moduleAnnotations
    srcs               = topmoduleAnnots ^. sources
    snks               = HS.toList $ topmoduleAnnots ^. sinks
    aeVars             = topmoduleAnnots ^. alwaysEquals

    topModule          = fromJust $ moduleMap ^. at topmoduleName
    topModuleIdCheck   = (`elem` (getData <$> alwaysBlocks topModule))
    ModuleSummary {..} = fromJust $ summaryMap ^. at topmoduleName

    toNode             = (variableDependencyNodeMap HM.!)
    toName             = (invVariableDependencyNodeMap IM.!)

    trc :: Show a => String -> a -> a
    trc msg a =
      let enableTrace = False
      in  if enableTrace then DT.trace (msg ++ show a) a else a

    isCT varName =
      let v = T.unpack varName
          helper (FSM.TraceConstantTime tv) = toTVName tv == v
          helper _                          = False
      in  any (any helper) lastTraceElem
    getCTNo v =
      if   v `elem` srcs || (v `elem` temporaryVariables && allChildrenAreCT v)
      then Nothing
      else btmLookupF topModuleIdCheck btm Q_CT v <|> if isCT v then Nothing else Just 0

    allChildrenAreCT v =
      let go (c, Explicit _) = isNothing $ getCTNo c
          go (_, Implicit)   = False
      in all go $ getVariableDependencies v topModule summaryMap

    insNode n a g = if G.gelem n g then g else G.insNode (n, a) g

    getDeps v = getVariableDependencies v topModule summaryMap

    createDepTree :: (Id -> Maybe Int) -> TstG -> Id -> Ids -> (TstG, Ids)
    createDepTree getIterNo g parentName ws
      |
      --  | DT.trace (unlines [ show $ toName <$> G.nodes g
      --                     , show parentName
      --                     , show $ toList ws]) False = undefined
        HS.member parentName ws
      = (g, ws)
      | otherwise
      = case
          trc (printf "parentCtNo (%s): " parentName) $ getIterNo parentName
        of
          Nothing -> (g, ws)
          Just parentIterNo ->
            let
              childrenNodes = trc (printf "childrenNodes of %s: " parentName)
                $ getDeps parentName
              nonCTChildren =
                [ (childName, fromJust childIterNo, depType)
                | (childName, depType) <- childrenNodes
                , let
                  childIterNo = trc (printf "childCtNo (%s) : " childName)
                    $ getIterNo childName
                , isJust childIterNo
                ]
              go acc@(g2, ws2) (childName, childIterNo, edgeType) =
                if childIterNo <= parentIterNo || parentIterNo == 0
                  then
                    let
                      childNode  = toNode childName
                      parentNode = toNode parentName
                      e          = (parentNode, childNode, edgeType)
                      g3 =
                        insEdge e $ insNode parentNode parentIterNo $ insNode
                          childNode
                          childIterNo
                          g2
                    in
                      -- DT.trace (
                      --   printf "Adding edge (%s, %s) since %d >= %d\n"
                      --          parentName
                      --          childName
                      --          parentIterNo
                      --          childIterNo
                      -- ) $
                      createDepTree getIterNo g3 childName ws2
                  else acc
              acc' = (g, HS.insert parentName ws)
            in
              foldl' go acc' nonCTChildren

  let createSinkTree = createDepTree getCTNo
  let
    toDotStr = GD.showDot . GD.fglToDotString . G.gmap
      (\(ps, n, a, ss) ->
        let
          lbl =
            printf "%s (%s)" (T.unpack (invVariableDependencyNodeMap IM.! n)) a
        in  (ps, n, lbl, ss)
      )
  let isPublic varName =
        let v = T.unpack varName
            helper (FSM.TracePublic tv) = toTVName tv == v
            helper _                    = False
        in  any (any helper) lastTraceElem
  let
    allChildrenArePub v =
      all (isNothing . getPubNo . fst) $ getVariableDependencies v topModule summaryMap
    getPubNo v =
       if  (v `elem` temporaryVariables && allChildrenArePub v) || v `elem` aeVars
       then Nothing
       else btmLookupF topModuleIdCheck btm Q_PUB v <|>
            if isPublic v then Nothing else Just 0

  let getLeaves = getLeafLikeNodes

  let hasToBePublic leaf =
        HS.fromList
          $ [ (childName, fromJust pn)
            | (childName, depType) <- getDeps leaf
            , depType == Implicit
            , let pn = getPubNo childName
            , isJust pn
            ]
  let initTree = foldl' (\g (v, n) -> insNode (toNode v) n g) G.empty
  let nonCtTreeLoop roots initws =
        let (finalTree, _finalWS) = foldl'
              (\(g, ws) (snk, _) -> createSinkTree g snk ws)
              (initTree roots, initws)
              roots
        in finalTree
  let nonCtTree =
        nonCtTreeLoop [ (s, n) | s <- snks, n <- toList (getCTNo s) ] mempty
  let showEdge Implicit         = "imp"
      showEdge (Explicit True ) = "exp-nb"
      showEdge (Explicit False) = "exp-b"

  let nonCtTreeLeaves =
        filter ((> 0) . snd) $
        first toName <$>
        getLeaves nonCtTree

  putStrLn "### NON CT TREE LEAVES ##########################################################"
  for_ nonCtTreeLeaves print
  putStrLn ""

  let minCtTreeLeaf@(minCtTreeLeafName, _) = swap $ minimum $ swap <$> nonCtTreeLeaves
  printf "Min leaf: %s\n\n" minCtTreeLeafName
  -- printf "Non public min leaf dependencies: %s\n\n"
  --   (show $ fmap fst $ HS.toList $ hasToBePublic minCtTreeLeafName)

  writeFile "nonCtTree.dot" $ toDotStr $ G.nemap show showEdge $
    let nodesToKeep = G.reachable (toNode minCtTreeLeafName) $ G.grev nonCtTree
    in G.nfilter (`elem` nodesToKeep) nonCtTree
  system "dot -Tpdf nonCtTree.dot -o nonCtTree.pdf"

  let
    createPubTree   = createDepTree getPubNo
    nonPubTreeRoots = {- nonCtTreeLeaves -} [minCtTreeLeaf] >>= HS.toList . hasToBePublic . fst
    iterToConstraintType iterNo = do
      constraintNo   <- fst <$> fpTrace ^. at iterNo
      constraintType <- cm ^. at constraintNo
      return $ hcType constraintType
    nonPubTree0 = fst $ foldl' (\(g, ws) (v, _) -> createPubTree g v ws)
                               (initTree nonPubTreeRoots, mempty)
                               nonPubTreeRoots
    nonPubTreeInitLeaves =
      [ toName l
      | (l, _lbl) <- getLeaves nonPubTree0
      , hid <- toList $ iterToConstraintType $ G.lab' $ G.context nonPubTree0 l
      , hid == Init
      ]

  putStrLn "### NON PUBLIC TREE ROOTS ######################################################"
  for_ nonPubTreeRoots (putStrLn . T.unpack . fst)
  putStrLn ""

  let isReg v = Register v `elem` variables topModule
  let nonPubTreeLoop :: TstG -> [Id] -> Ids -> TstG
      nonPubTreeLoop g [] _ = g
      nonPubTreeLoop g (leaf : leaves) ws | leaf `elem` ws || isReg leaf =
        nonPubTreeLoop g leaves ws
      nonPubTreeLoop g (wire : leaves) ws =
        let
          _newEdges =
            [ (wire, v, typ)
            | (v, typ) <- getDeps wire
            , not (isReg v)
              || (         v
                 `notElem` topmoduleAnnots
                 ^.        initialEquals
                 &&        v
                 `notElem` topmoduleAnnots
                 ^.        alwaysEquals
                 )
            ]
          newEdges = -- DT.trace ("new edges: " ++ show _newEdges)
            [ (toNode x, toNode y, z) | (x, y, z) <- _newEdges ]
          g' =
            foldl' (\acc e@(_, n, _) -> insEdge e $ insNode n 0 acc) g newEdges
        in
          nonPubTreeLoop g' leaves (HS.insert wire ws)
  let nonPubTree = nonPubTreeLoop nonPubTree0 nonPubTreeInitLeaves mempty
  writeFile "nonPubTree.dot" $ toDotStr $ G.nemap
    (\n ->
      (if iterToConstraintType n == Just Init then "Init " else "")
        <> "#"
        <> show n
    )
    showEdge
    nonPubTree
  system "dot -Tpdf nonPubTree.dot -o nonPubTree.pdf"

  return ()

getLeafLikeNodes :: Eq b => G.Gr a b -> [G.LNode a]
getLeafLikeNodes g = (\n -> (n, fromJust $ G.lab g n)) <$> ls
 where
  (sccG, _) = sccGraph g
  go acc (sccN, sccNs) = if G.outdeg sccG sccN == 0 then acc <> sccNs else acc
  ls = IS.toList (foldl' go mempty (G.labNodes sccG))
