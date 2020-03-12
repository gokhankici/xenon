{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Analyze.ModuleSummary
  (
    createModuleSummaries
  -- , tryToSummarize
  , ModuleSummary(..)
  , SummaryMap
  )
where

import           Iodine.Analyze.DependencyGraph
import           Iodine.Analyze.ModuleDependency
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive.Query as GQ
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntSet as IS
import qualified Data.Sequence as SQ
import           Data.Traversable
import           Polysemy
import qualified Polysemy.Error as PE
import           Polysemy.Reader
import           Polysemy.State
import qualified Polysemy.Trace as PT

type M           = Module Int
type ModuleMap   = HM.HashMap Id M
type SummaryMap  = HM.HashMap Id ModuleSummary
type TDGraph     = G.Gr () () -- | thread dependency graph
type Error       = PE.Error IodineException

data ModuleSummary =
  ModuleSummary { -- | the dependency map between ports: from an output to the
                  -- set of inputs that affect it
                  portDependencies :: HM.HashMap Id Ids,

                  -- ^ whether the module is a combinational logic (i.e., does
                  isCombinatorial :: Bool,

                  -- | (t1, t2) \in E <=> thread t1 updates a variable that
                  -- thread t2 uses
                  threadDependencies :: TDGraph
                  }
  deriving (Show)

-- #############################################################################

{- |
Create a summary for each given module
-}
createModuleSummaries :: Members '[ Reader AnnotationFile
                                  , PT.Trace
                                  , Error
                                  , Reader ModuleMap
                                  ] r
                      => ModuleMap -> Sem r SummaryMap
createModuleSummaries moduleMap =
  for_ orderedModules (\m@Module{..} ->
      createModuleSummary m >>= (modify . HM.insert moduleName))
  & runState @SummaryMap mempty
  & fmap fst
  where
    orderedModules = topsortModules moduleMap


createModuleSummary :: Members '[ Reader AnnotationFile
                                , State SummaryMap
                                , PT.Trace
                                , Error
                                , Reader ModuleMap
                                ] r
                    => M
                    -> Sem r ModuleSummary
createModuleSummary m@Module{..} = do
  (varDepGraph, varDepMap, threadGr) <- dependencyGraphFromModule m
  trace "createModuleSummary-module" moduleName
  let lookupNode v = mapLookup 1 v varDepMap
  clks <- getClocks moduleName
  let hasClock = not $ HS.null clks
      isClk v = v `elem` clks
  let portDependencies =
        foldl'
        (\deps o ->
           let is = HS.fromList $ toList $
                    SQ.filter
                    (\i -> not (isClk i) && (isReachable varDepGraph (lookupNode o) . lookupNode) i)
                    inputs
           in  HM.insert o is deps)
        mempty
        outputs

  -- we can summarize the module instance if itself does not have a clock and
  -- all of its submodules can be summarized
  submodulesCanBeSummarized <-
    fmap and $
    forM moduleInstances $ \ModuleInstance{..} ->
    isCombinatorial <$> gets (mapLookup 2 moduleInstanceType)
  let isCombinatorial = not hasClock && submodulesCanBeSummarized

  return $ ModuleSummary portDependencies isCombinatorial threadGr
  where
    isReachable g toNode fromNode =
      let ns = GQ.reachable fromNode g
      in toNode `elem` ns

    inputs, outputs :: L Id
    (inputs, outputs) =
      foldl' (\acc -> \case
                 Input i  -> acc & _1 %~ (|> variableName i)
                 Output o -> acc & _2 %~ (|> variableName o)) mempty ports


dependencyGraphFromModule :: Members '[ State SummaryMap
                                      , Error
                                      , PT.Trace
                                      , Reader AnnotationFile
                                      , Reader ModuleMap
                                      ] r
                          => M
                          -> Sem r (VarDepGraph, HM.HashMap Id Int, ThreadDepGraph)
dependencyGraphFromModule Module{..} =
  if   SQ.null moduleInstances
  then return (g, nodeMap, tg)
  else do
    unless (SQ.null gateStmts) (PE.throw $ IE Analysis "non null gate stmts")
    (tg', (nodeMap', extraEdges)) <- runState tg $ runState nodeMap $ evalState maxId $
                              foldlM' SQ.empty moduleInstances $ \es mi@ModuleInstance{..} -> do
      let miThreadId = getData mi
      modify (G.insNode (miThreadId, ()))
      miModule <- asks (HM.! moduleInstanceType)
      miClocks <- getClocks moduleInstanceType
      let miInputs = moduleInputs miModule miClocks
          miOutputs = moduleOutputs miModule miClocks
          lookupThreads p optic =
            let e = moduleInstancePorts HM.! p
                vs = getVariables e
            in do v <- toList vs
                  concat $ IS.toList <$> HM.lookup v (dgState ^. optic)
      -- FIXME
      for_ miInputs $ \p ->
        for_ (lookupThreads p varUpdates) $ \wt ->
        modify (G.insEdge (wt, miThreadId, ()))
      for_ miOutputs $ \p ->
        for_ (lookupThreads p varReads) $ \rt ->
        modify (G.insEdge (miThreadId, rt, ()))

      ModuleSummary{..} <- gets (mapLookup 3 moduleInstanceType)
      let assignedVars p = toSequence . getVariables $ mapLookup 4 p moduleInstancePorts
          tmpEdges = do (o, is) <- toSequence $ HM.toList portDependencies
                        i <- toSequence is
                        fromVar <- assignedVars i
                        toVar   <- assignedVars o
                        return (fromVar, toVar)
      es' <- for tmpEdges $ \(fromVar, toVar) -> do
        fromNode <- getNode fromVar
        toNode <- getNode toVar
        return (fromNode, toNode, Explicit Blocking)
      return $ es <> es'
    trace "thread graph" tg'
    return (foldr' G.insEdge g extraEdges, nodeMap', tg')
  where
    maxId = maximum $ HM.elems nodeMap
    dgState = dependencyGraph alwaysBlocks
    g       = dgState ^. depGraph
    nodeMap = dgState ^. varMap
    tg      = dgState ^. threadGraph

getNode :: Members '[State (HM.HashMap Id Int), State Int] r => Id -> Sem r Int
getNode nodeName = do
  mNodeId <- gets (HM.lookup nodeName)
  case mNodeId of
    Nothing -> do
      newId <- gets (+ 1)
      modify (HM.insert nodeName newId)
      put newId
      return newId
    Just n  -> return n

mapLookup :: Show a => Int -> Id -> HM.HashMap Id a -> a
mapLookup n k m =
  case HM.lookup k m of
    Nothing ->
      error $ unlines [ "ModuleSummary.mapLookup: " ++ show n
                      , "map: " ++ show m
                      , "key:" ++ show k
                      ]
    Just a  -> a

trace :: (Members '[PT.Trace] r, Show a) => String -> a -> Sem r ()
trace msg a = PT.trace msg >> PT.trace (show a)
