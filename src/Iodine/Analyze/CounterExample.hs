{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}

module Iodine.Analyze.CounterExample
  ( readFixpointTrace
  , toTVName
  , firstNonCT
  , ConstraintTypes
  , toConstraintTypes
  , QualType(..)
  , btmLookup
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
import           Control.Monad
import           Data.Foldable
import qualified Data.Graph.Inductive          as G
import qualified Data.Graph.Inductive.Dot      as GD
import qualified Data.HashMap.Strict           as HM
import qualified Data.HashSet                  as HS
import           Data.Hashable
import qualified Data.IntMap                   as IM
import           Data.Maybe
import qualified Data.Text                     as T
import qualified Language.Fixpoint.Solver.Monad
                                               as FSM
import           System.Exit
import           Text.Printf
import           GHC.Generics            hiding ( moduleName )
import qualified Debug.Trace                   as DT
import           System.Process
import qualified Language.Fixpoint.Types       as FT

type ConstraintTypes = IM.IntMap HornClauseId
type ModuleMap = HM.HashMap Id (Module Int)
type TstG = G.Gr Int VarDepEdgeType
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
btmLookup btm qt varName = do
  kvs <- {- trc (printf "getCTNo qs (%s): " varName) $ -}
         btm ^. at varName
  case IM.toList kvs of
    [(_tid, m)] -> m ^. at qt
    qsList ->
      case
          [ iterNo | (_tid, m) <- qsList, iterNo <- toList $ HM.lookup qt m ]
        of
          [] -> Nothing
          i : is ->
            -- DT.trace (printf "Multiple iterNos for %s: %s" varName (show $ i:is)) $
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
    snks               = HS.toList $ topmoduleAnnots ^. sinks

    topModule          = fromJust $ moduleMap ^. at topmoduleName
    ModuleSummary {..} = fromJust $ summaryMap ^. at topmoduleName

    toNode             = (variableDependencyNodeMap HM.!)
    toName             = (invVariableDependencyNodeMap IM.!)

    trc :: Show a => String -> a -> a
    trc msg a = DT.trace (msg ++ show a) a

    isCT varName =
      let v = T.unpack varName
          helper (FSM.TraceConstantTime tv) = toTVName tv == v
          helper _                          = False
      in  any (any helper) lastTraceElem
    getCTNo v = btmLookup btm Q_CT v <|> if isCT v then Nothing else Just 0

    insNode n a g = if G.gelem n g then g else G.insNode (n, a) g

    insEdge' e@(n1, n2, _edgeType) g =
      if n1 `elem` G.reachable n2 g then g else insEdge e g

    getDeps v = getVariableDependencies v topModule summaryMap

    createDepTree :: (Id -> Maybe Int) -> TstG -> Id -> Ids -> (TstG, Ids)
    createDepTree getIterNo g parentName ws
      | HS.member parentName ws = (g, ws)
      | otherwise = case {- trc (printf "parentCtNo (%s): " currentVarName) $ -}
                         getIterNo parentName of
        Nothing -> (g, ws)
        Just parentIterNo ->
          let
            childrenNodes = {- trc (printf "childrenNodes of %s: " currentVarName) $ -}getDeps parentName
            nonCTChildren =
              [ (childName, fromJust childIterNo, depType)
              | (childName, depType) <- childrenNodes
              , let childIterNo = {- trc (printf "childCtNo (%s) : " childName) $ -}getIterNo childName
              , isJust childIterNo
              ]
            go acc@(g2, ws2) (childName, childIterNo, edgeType) =
              if childIterNo <= parentIterNo
                then
                  let
                    childNode  = toNode childName
                    parentNode = toNode parentName
                    e          = (parentNode, childNode, edgeType)
                    g3 = insEdge' e $ insNode parentNode parentIterNo $ insNode
                      childNode
                      childIterNo
                      g2
                  in
                    -- DT.trace
                    --     (printf "Adding edge (%s, %s) since %d >= %d"
                    --             parentName
                    --             childName
                    --             parentIterNo
                    --             childIterNo
                    --     ) $
                    createDepTree getIterNo g3 childName ws2
                else acc
            acc' = (g, HS.insert parentName ws)
          in
            foldl' go acc' nonCTChildren

  print snks
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
  let getPubNo v =
        btmLookup btm Q_PUB v <|> if isPublic v then Nothing else Just 0
  let getLeaves g =
        foldl' (\acc n -> if G.outdeg g n == 0 then n : acc else acc) []
          $ G.nodes g

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
        let
          (finalTree, finalWS) = foldl'
            (\(g, ws) (snk, _) -> createSinkTree g snk ws)
            (initTree roots, initws)
            roots
          nonCtTreeLeaves = toName <$> getLeaves finalTree
          allNonCtChildrenAreGreater l =
            let lIterNo  = fromJust $ getCTNo l
                childNos = getCTNo . fst <$> getDeps l
            in  any (/= Nothing) childNos
                  && all (maybe True (> lIterNo)) childNos
          needsFixin l = allNonCtChildrenAreGreater l && null (hasToBePublic l)
          rootsToFix = trc "rootsToFix: " $ filter needsFixin nonCtTreeLeaves
        -- FIXME
        in
          if True -- null rootsToFix
            then finalTree
            else
              let roots' =
                    [ (c, n)
                    | r      <- rootsToFix
                    , (c, _) <- getDeps r
                    , n      <- toList $ getCTNo c
                    ]
              in  nonCtTreeLoop
                    roots'
                    (foldl' (flip HS.delete) finalWS (fst <$> roots'))
  let nonCtTree =
        nonCtTreeLoop [ (s, n) | s <- snks, n <- toList (getCTNo s) ] mempty
  writeFile "nonCtTree.dot" $ toDotStr $ G.nemap show show nonCtTree
  system "dot -Tpdf nonCtTree.dot -o nonCtTree.pdf"

  let shouldNotHaveCycle g msg =
        unless (length (G.nodes g) == length (G.scc g)) $ do
          putStrLn msg
          exitFailure

  shouldNotHaveCycle nonCtTree "ct tree has a cycle!"
  let nonCtTreeLeaves = toName <$> getLeaves nonCtTree
  printf "NON CT TREE LEAVES: %s\n" (show nonCtTreeLeaves)

  let createPubTree = createDepTree getPubNo
  let nonPubTreeRoots =
        [ c
        | l <- nonCtTreeLeaves
        , c <- HS.toList $ hasToBePublic l
        ]
  let iterToConstraintType iterNo = do
        constraintNo   <- fst <$> fpTrace ^. at iterNo
        constraintType <- cm ^. at constraintNo
        return $ hcType constraintType
  let nonPubTree0 = fst $ foldl' (\(g, ws) (v, _) -> createPubTree g v ws)
                                 (initTree nonPubTreeRoots, mempty)
                                 nonPubTreeRoots
  let
    nonPubTreeInitLeaves =
      [ toName l
      | l   <- getLeaves nonPubTree0
      , hid <- toList $ iterToConstraintType $ G.lab' $ G.context nonPubTree0 l
      , hid == Init
      ]
  printf "NON PUBLIC TREE ROOTS: %s\n" (show nonPubTreeRoots)
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
          newEdges = DT.trace
            ("new edges: " ++ show _newEdges)
            [ (toNode x, toNode y, z) | (x, y, z) <- _newEdges ]
          g' =
            foldl' (\acc e@(_, n, _) -> insEdge' e $ insNode n 0 acc) g newEdges
        in
          nonPubTreeLoop g' leaves (HS.insert wire ws)
  let nonPubTree = nonPubTreeLoop nonPubTree0 nonPubTreeInitLeaves mempty
  shouldNotHaveCycle nonPubTree "public tree has a cycle!"
  writeFile "nonPubTree.dot" $ toDotStr $ G.nemap
    (\n ->
      (if iterToConstraintType n == Just Init then "Init " else "")
        <> "#"
        <> show n
    )
    show
    nonPubTree
  system "dot -Tpdf nonPubTree.dot -o nonPubTree.pdf"

  return ()
