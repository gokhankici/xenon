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

import           Iodine.ConstantConfig
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
import           Data.List
import           Control.Monad
import           Iodine.Analyze.ILP

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
  :: AnnotationFile -> ModuleMap -> SummaryMap -> FInfo -> Bool -> IO ()
--------------------------------------------------------------------------------
generateCounterExampleGraphs af moduleMap summaryMap finfo enableAbductionLoop = do
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
  let nonCtTree = nonCtTreeLoop [ (s, n) | s <- snks, n <- toList (getCTNo s) ] mempty

  let nonCtTreeLeaves =
        fmap (first toName) <$>
        getLeaves nonCtTree

  putStrLn "### NON CT TREE LEAVES ##########################################################"
  for_ nonCtTreeLeaves $ \l -> for_ l print >> putStrLn ""

  let minCtTreeLeaves0 =
        let getMinRegNo l =
              case find ((> 0) . snd) l of
                Nothing     -> 0
                Just (_, i) -> i
            cmp2 (_,i1) (_,i2) = compare i1 i2
            clustersWithMinIterNos = (\l -> (l, getMinRegNo l)) . sortBy cmp2 <$> nonCtTreeLeaves
            minClusterIterNo = getMinRegNo clustersWithMinIterNos
        in nub' id
           [ l
           | (c, i) <- clustersWithMinIterNos
           , i == minClusterIterNo
           , l <- c
           ]
  let minCtTreeLeaves =
        if includeEveryVariable
        then let leafIterNos = foldl' (\acc (_v,n) -> IS.insert n acc) mempty minCtTreeLeaves0
             in [ (toName n, i)
                | n <- G.nodes nonCtTree
                , let i = fromJust $ G.lab nonCtTree n
                , i `IS.member` leafIterNos
                ]
        else minCtTreeLeaves0
  printf "Min leaves: %s\n\n" $ show $ fst <$> minCtTreeLeaves

  let toCtTreeDotStr =
        toDotStr
        (invVariableDependencyNodeMap IM.!)
        (\i -> if i >= 0 then printf " #%d" i else "")
        edgeStyle

  writeFile "nonCtTree.dot" $
    let revG         = G.grev nonCtTree
        go ntk (v,_) = ntk <> IS.fromList (G.reachable (toNode v) revG)
        nodesToKeep  = foldl' go IS.empty minCtTreeLeaves
        subG = G.nfilter (`IS.member` nodesToKeep) revG
    in toCtTreeDotStr subG
  callDot "nonCtTree.dot" "nonCtTree.pdf"

  let
    createPubTree   = createDepTree getPubNo
    nonPubTreeRoots = nub' id $ minCtTreeLeaves >>= HS.toList . hasToBePublic . fst
    iterToConstraintType iterNo = do
      constraintNo   <- fst <$> fpTrace ^. at iterNo
      constraintType <- cm ^. at constraintNo
      return $ hcType constraintType
    nonPubTree0 = fst $ foldl' (\(g, ws) (v, _) -> createPubTree g v ws)
                               (initTree nonPubTreeRoots, mempty)
                               nonPubTreeRoots
    nonPubTreeInitLeaves =
      [ toName l
      | ls  <- getLeaves nonPubTree0
      , (l, _lbl) <- ls
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
  let nonPubTree = G.grev $ nonPubTreeLoop nonPubTree0 nonPubTreeInitLeaves mempty
  writeFile "nonPubTree.dot" $ toDotStr (invVariableDependencyNodeMap IM.!)
    (\i ->
      if iterToConstraintType i == Just Init
      then " (Init #" <> show i <> ")"
      else " (" <> show i <> ")"
    )
    edgeStyle
    nonPubTree
  callDot "nonPubTree.dot" "nonPubTree.pdf"

  let regsInPubTree =
        (HS.fromList $ filter isReg $ toName <$> G.nodes nonPubTree)
        `HS.difference`
        (topmoduleAnnots ^. initialEquals)
  unless (null regsInPubTree) $ do
    putStrLn "Try sanitizing these registers"
    print $ toList regsInPubTree

  let ilpGraph       = nonPubTree
      mustBePublic   = toNode . fst <$> nonPubTreeRoots
      cannotBeMarked = []
      loops = let (pubSCC, _) = sccGraph ilpGraph
              in [ IS.toList l
                 | n <- G.nodes pubSCC
                 , l <- toList (G.lab pubSCC n)
                 , IS.size l > 0
                 ]
  ilpResult <- if enableAbductionLoop
               then runILPLoop mustBePublic cannotBeMarked loops ilpGraph toName
               else runILP mustBePublic cannotBeMarked loops ilpGraph
  case ilpResult of
    Left errMsg -> putStrLn errMsg
    Right (pubNodes, markedNodes) -> do
      let sep = putStrLn $ replicate 80 '-'
      sep
      if null markedNodes
        then do putStrLn "\n\nHuh, there are no nodes to mark ..."
                putStrLn "Maybe you should mark these non-constant-time leaf variables as public:"
                print $ fst <$> minCtTreeLeaves
        else putStrLn "marked nodes:" >> print (toName <$> markedNodes)
      sep
      putStrLn "initial_eq candidates:"
      print $ filter (isJust . getPubNo) (toName <$> pubNodes)
      sep
  writeFile "nonPubTreeSCC.dot" $
    toDotStr (\n -> toName n <> " : " <> T.pack (show n)) (const "") edgeStyle ilpGraph
  callDot "nonPubTreeSCC.dot" "nonPubTreeSCC.pdf"

  -- writeFile "nonCtTree-full.dot" $
  --   let completeNonCtGraph =
  --         G.gmap (\(ps, n, _a, cs) ->
  --           let a = fromMaybe (-1) $ getCTNo (toName n)
  --           in (ps, n, a, cs)
  --         ) variableDependencies
  --   in toCtTreeDotStr completeNonCtGraph
  -- callDot "nonCtTree-full.dot" "nonCtTree-full.pdf"

  return ()

callDot :: String -> String -> IO ()
callDot i o = do
  system $ printf "dot -Tpdf -Gmargin=0 '%s' -o '%s'" i o
  return ()

getLeafLikeNodes :: Eq b => G.Gr a b -> [[G.LNode a]]
getLeafLikeNodes = getLLNHelper G.outdeg

getLLNHelper :: Eq b => (forall c d. G.Gr c d -> Int -> Int) -> G.Gr a b -> [[G.LNode a]]
getLLNHelper f g = fmap (\n -> (n, fromJust $ G.lab g n)) <$> ls
 where
  (sccG, _) = sccGraph g
  go acc (sccN, sccNs) = if f sccG sccN == 0 then IS.toList sccNs : acc else acc
  ls = foldl' go mempty (G.labNodes sccG)

edgeStyle :: VarDepEdgeType -> String
edgeStyle Implicit     = "dashed"
edgeStyle (Explicit _) = "solid"