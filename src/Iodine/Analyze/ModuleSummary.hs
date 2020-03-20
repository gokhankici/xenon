{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Analyze.ModuleSummary
  (
    createModuleSummaries
  , getAllDependencies
  , ModuleSummary(..)
  , SummaryMap
  )
where

import           Iodine.Analyze.DependencyGraph hiding (getNode)
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
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Sequence as SQ
import           Data.Traversable
import           Polysemy
import qualified Polysemy.Error as PE
import           Polysemy.Reader
import           Polysemy.State
import qualified Polysemy.Trace as PT

type ModuleMap   = HM.HashMap Id (Module Int)
type SummaryMap  = HM.HashMap Id ModuleSummary
type TDGraph     = G.Gr () () -- | thread dependency graph
type Error       = PE.Error IodineException

data ModuleSummary =
  ModuleSummary { -- | the dependency map between ports: from an output to the
                  -- set of inputs that affect it
                  portDependencies :: HM.HashMap Id Ids,

                  -- | whether the module is a combinational logic (i.e., does
                  isCombinatorial :: Bool,

                  -- | if the module does not have a clock, this contains the
                  -- registers that are being read before written (i.e., the
                  -- internal state of the module). Otherwise, this is empty.
                  readBeforeWrittenVars :: Ids,

                  -- | (t1, t2) \in E <=> thread t1 updates a variable that
                  -- thread t2 uses
                  threadDependencies :: TDGraph,

                  -- | maps variables to threads that read it
                  threadReadMap :: HM.HashMap Id IS.IntSet,

                  -- | maps variables to threads that update it
                  threadWriteMap :: HM.HashMap Id IS.IntSet,

                  -- | variable dependency map
                  variableDependencies :: VarDepGraph,

                  -- | variable name -> node id
                  variableDependencyNodeMap  :: HM.HashMap Id Int,

                  -- | node id -> variable name
                  invVariableDependencyNodeMap :: IM.IntMap Id
                  }
  deriving (Show)

-- #############################################################################

{- |
Create a summary for each given module
-}
createModuleSummaries :: Members '[ Reader AnnotationFile
                                  , PT.Trace
                                  , Error ] r
                      => ModuleMap -> Sem r SummaryMap
createModuleSummaries moduleMap =
  -- trace "ordered modules" (moduleName <$> orderedModules)
  for_ orderedModules (\m@Module{..} ->
                          createModuleSummary m >>= (modify . HM.insert moduleName))
    & runReader moduleMap
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
                    => Module Int
                    -> Sem r ModuleSummary
createModuleSummary m@Module{..} = do
  dgState <- dependencyGraphFromModule m
  let varDepGraph = dgState ^. depGraph
      varDepMap   = dgState ^. varMap
  -- trace "createModuleSummary-module" moduleName
  -- trace
  --   ("thread dependencies of module #" ++ show (getData m))
  --   (G.edges $ dgState ^. threadGraph)
  let lookupNode v = mapLookup 1 v varDepMap
  clks <- getClocks moduleName
  let hasClock = not $ HS.null clks
      isClk v = v `elem` clks
  let portDeps =
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
    for moduleInstances $ \ModuleInstance{..} ->
    isCombinatorial <$> gets (mapLookup 2 moduleInstanceType)

  allModuleInstanceOutputs <-
    mfoldM
    (\ModuleInstance{..} -> do
        outputPorts <-
          moduleOutputs
          <$> asks (HM.! moduleInstanceType)
          <*> getClocks moduleInstanceType
        return $
          HM.foldlWithKey'
          (\acc p e ->
             if p `elem` outputPorts
             then acc <> getVariables e
             else acc
          ) mempty moduleInstancePorts
    ) moduleInstances

  let readBeforeWrittenVars =
        if hasClock
        then mempty
        else case alwaysBlocks of
               SQ.Empty           -> mempty
               ab SQ.:<| SQ.Empty -> readBeforeWrittenTo (abStmt ab) allModuleInstanceOutputs
                                     `HS.difference` inputsSet
               _                  -> error "unreachable"
  -- trace ("readBeforeWrittenVars " ++ show moduleName) readBeforeWrittenVars

  let isComb =
        not hasClock &&
        submodulesCanBeSummarized &&
        HS.null readBeforeWrittenVars

  return $
    ModuleSummary
    { portDependencies             = portDeps
    , isCombinatorial              = isComb
    , readBeforeWrittenVars        = readBeforeWrittenVars
    , threadDependencies           = dgState ^. threadGraph
    , threadReadMap                = dgState ^. varReads
    , threadWriteMap               = dgState ^. varUpdates
    , variableDependencies         = varDepGraph
    , variableDependencyNodeMap    = varDepMap
    , invVariableDependencyNodeMap = IM.fromList $
                                     swap <$> HM.toList varDepMap
    }
  where
    isReachable g toNode fromNode =
      let ns = GQ.reachable fromNode g
      in toNode `elem` ns

    swap (a,b) = (b,a)

    inputsSet :: Ids
    inputsSet = toHSet inputs

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
                          => Module Int
                          -> Sem r DependencyGraphSt
dependencyGraphFromModule m@Module{..} =
  dependencyGraph m
  -- dgState <- dependencyGraph m
  -- if   SQ.null moduleInstances
  --   then return dgState
  --   else do
  --   let nodeMap = dgState ^. varMap
  --       maxId   = maximum $ HM.elems nodeMap
  --   unless (SQ.null gateStmts) (PE.throw $ IE Analysis "non null gate stmts")
  --   (nodeMap', extraEdges) <-
  --     runState nodeMap $ evalState maxId $
  --     foldlM' SQ.empty moduleInstances $ \es ModuleInstance{..} -> do
  --     ModuleSummary{..} <- gets (mapLookup 3 moduleInstanceType)
  --     let assignedVars p = toSequence . getVariables $ mapLookup 4 p moduleInstancePorts
  --         tmpEdges = do (o, is) <- toSequence $ HM.toList portDependencies
  --                       i <- toSequence is
  --                       fromVar <- assignedVars i
  --                       toVar   <- assignedVars o
  --                       return (fromVar, toVar)
  --     es' <- for tmpEdges $ \(fromVar, toVar) -> do
  --       fromNode <- getNode fromVar
  --       toNode <- getNode toVar
  --       return (fromNode, toNode, Explicit Blocking)
  --     return $ es <> es'
  --   -- trace "thread graph" $ dgState ^. threadGraph
  --   return $
  --     dgState
  --     & over depGraph (\g -> foldr' insEdge g extraEdges)
  --     & set varMap nodeMap'

-- getNode :: Members '[State (HM.HashMap Id Int), State Int] r => Id -> Sem r Int
-- getNode nodeName = do
--   mNodeId <- gets (HM.lookup nodeName)
--   case mNodeId of
--     Nothing -> do
--       newId <- gets (+ 1)
--       modify (HM.insert nodeName newId)
--       put newId
--       return newId
--     Just n  -> return n

mapLookup :: Show a => Int -> Id -> HM.HashMap Id a -> a
mapLookup n k m =
  case HM.lookup k m of
    Nothing ->
      error $ unlines [ "ModuleSummary.mapLookup: " ++ show n
                      , "map: " ++ show m
                      , "key:" ++ show k
                      ]
    Just a  -> a


type GAD r = Members '[ Reader ModuleSummary
                      , Reader (IM.IntMap (Thread Int))
                      ] r

-- | returns the transitive closure of the id of the threads that update the
-- given thread
getAllDependencies :: GAD r => Thread Int -> Sem r IS.IntSet
getAllDependencies thread =
  execState mempty $
  asks ((`G.pre` getData thread) . threadDependencies)
  >>= traverse_ getAllDependencies'


getAllDependencies' :: (GAD r, Members '[State IS.IntSet] r) => Int -> Sem r ()
getAllDependencies' fromThreadId = do
  threadInSet <- gets (IS.member fromThreadId)
  unless threadInSet $ do
    modify (IS.insert fromThreadId)
    fromThread <- asks (IM.! fromThreadId)
    unless (isAB fromThread) $
      asks ((`G.pre` fromThreadId) . threadDependencies)
      >>= traverse_ getAllDependencies'

readBeforeWrittenTo :: Stmt Int -> Ids -> Ids
readBeforeWrittenTo stmt initialWrittenVars = readBeforeWrittenSet
  where
    (_readSet, _writeSet, readBeforeWrittenSet) =
      go stmt
      & execState (mempty, initialWrittenVars, mempty)
      & run

    go :: Members '[State (Ids, Ids, Ids)] r => Stmt Int -> Sem r ()
    go Block{..} = traverse_ go blockStmts
    go Skip{}    = return ()

    go Assignment{..} = do
      newReadVars <- mappend (getVariables assignmentRhs) <$> gets (view _1)
      writtenVars <- gets (view _2)
      let writtenVar = varName assignmentLhs
      when (writtenVar `notElem` writtenVars &&
            writtenVar `elem` newReadVars) $
        modify $ _3 %~ HS.insert writtenVar
      modify $ _1 .~ newReadVars
      modify $ _2 %~ HS.insert writtenVar

    go IfStmt{..} = do
      oldWrittenVars <- gets (view _2)
      let newReadVars = getVariables ifStmtCondition
      modify $ _3 %~ HS.union (newReadVars `HS.difference` oldWrittenVars)
      readVars <- mappend newReadVars <$> gets (view _1)

      modify $ _1 .~ readVars
      go ifStmtThen
      readVarsThen   <- gets (view _1)
      writtenVarsThen <- gets (view _2)

      modify $ _1 .~ readVars
      modify $ _2 .~ oldWrittenVars
      go ifStmtElse
      readVarsElse    <- gets (view _1)
      writtenVarsElse <- gets (view _2)

      modify $ _1 .~ (readVarsThen `HS.intersection` readVarsElse)
      modify $ _2 .~ (writtenVarsThen `HS.intersection` writtenVarsElse)
