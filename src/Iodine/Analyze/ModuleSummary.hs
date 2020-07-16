{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Iodine.Analyze.ModuleSummary
  ( createModuleSummaries
  , getAllDependencies
  , ModuleSummary(..)
  , SummaryMap
  , readBeforeWrittenTo
  , QualifierDependencies
  , explicitVars
  , implicitVars
  , addPortDependencies
  , getVariableDependencies
  ) where

import           Iodine.Analyze.DependencyGraph hiding (getNode)
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Effect.Lens (use)
import           Control.Lens hiding (use)
import           Control.Monad
import           Data.Bifunctor
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import           Data.Maybe
import qualified Data.Sequence as SQ
import           Data.Traversable

data QualifierDependencies = QualifierDependencies
  { _explicitVars :: Ids
  , _implicitVars :: Ids
  }
  deriving (Eq, Show, Read)

makeLenses ''QualifierDependencies

type ModuleMap        = HM.HashMap Id (Module Int)
type TDGraph          = G.Gr () () -- ^ thread dependency graph
type SummaryMap       = HM.HashMap Id ModuleSummary
type PortDependencies = HM.HashMap Id QualifierDependencies

data ModuleSummary =
  ModuleSummary { -- | the dependency map between ports: from an output to the
                  -- set of inputs that affect it
                  portDependencies :: PortDependencies,

                  -- | whether the module is a combinational logic (i.e., does
                  isCombinatorial :: Bool,

                  -- | (t1, t2) \in E <=> thread t1 updates a variable that
                  -- thread t2 uses
                  threadDependencies :: TDGraph,

                  -- | maps variables to threads that update it
                  -- threadWriteMap :: HM.HashMap Id IS.IntSet,
                  threadWriteMap :: HM.HashMap Id Int,

                  -- | variable dependency map
                  variableDependencies :: VarDepGraph,

                  -- | variable name -> node id
                  variableDependencyNodeMap  :: HM.HashMap Id Int,

                  -- | node id -> variable name
                  invVariableDependencyNodeMap :: IM.IntMap Id,

                  -- | variable dependency graph with SCC
                  variableDependenciesSCC       :: G.Gr IS.IntSet VarDepEdgeType,
                  variableDependencySCCNodeMap  :: IM.IntMap Int
                  }
  deriving (Show, Read)


-- #############################################################################

{- |
Create a summary for each given module
-}
createModuleSummaries :: ( Has (Reader AnnotationFile) sig m
                         -- , Effect sig
                         )
                      => L (Module Int) -- ^ modules (filtered & topologically sorted)
                      -> ModuleMap      -- ^ same modules, in a hash map
                      -> m SummaryMap
createModuleSummaries orderedModules moduleMap =
  -- trace "ordered modules" (moduleName <$> orderedModules)
  for_ orderedModules (\m@Module{..} ->
                          createModuleSummary m >>= (modify . HM.insert moduleName))
    & execState @SummaryMap mempty
    & runReader moduleMap


createModuleSummary :: ( Has (Reader AnnotationFile) sig m
                       , Has (State SummaryMap) sig m
                       , Has (Reader ModuleMap) sig m
                       -- , Effect sig
                       )
                    => Module Int
                    -> m ModuleSummary
createModuleSummary m@Module{..} = do
  dgState <- dependencyGraph m
  let varDepGraph = dgState ^. depGraph
      varDepMap   = dgState ^. varMap
  -- trace "createModuleSummary-module" moduleName
  -- trace
  --   ("thread dependencies of module #" ++ show (getData m))
  --   (G.edges $ dgState ^. threadGraph)
  clks <- getClocks moduleName
  let hasClock = not $ HS.null clks

  summaryMap <- get @SummaryMap
  let nodeMap = IM.fromList $ swap <$> HM.toList varDepMap
      varDepGraph' =
        foldl'
        (\g mi -> addPortDependencies mi g varDepMap
                  & runReader summaryMap & run
        ) varDepGraph moduleInstances

  let portDeps = moduleAnnots m varDepGraph' nodeMap varDepMap

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
          <$> asks @ModuleMap (hmGet 4 moduleInstanceType)
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
               ab SQ.:<| SQ.Empty -> readBeforeWrittenTo ab allModuleInstanceOutputs
                                     `HS.difference` inputsSet
               _                  -> error "unreachable"
  -- trace ("readBeforeWrittenVars " ++ show moduleName) readBeforeWrittenVars

  let isComb =
        not hasClock &&
        submodulesCanBeSummarized &&
        HS.null readBeforeWrittenVars

  let (sccG, toSCCNodeMap) = sccGraph varDepGraph

  return $
    ModuleSummary
    { portDependencies             = portDeps
    , isCombinatorial              = isComb
    , threadDependencies           = dgState ^. threadGraph
    , threadWriteMap               =
        let toSingle ts = case IS.toList ts of
                            [t] -> t
                            _ -> error $ "multiple update threads: " ++ show ts
        in toSingle <$> dgState ^. varUpdates
    , variableDependencies         = varDepGraph
    , variableDependencyNodeMap    = varDepMap
    , invVariableDependencyNodeMap = nodeMap
    , variableDependenciesSCC      = sccG
    , variableDependencySCCNodeMap = toSCCNodeMap
    }
  where
    swap (a,b) = (b,a)
    inputsSet = moduleInputs m mempty

addPortDependencies :: Has (Reader SummaryMap) sig m
                    => ModuleInstance Int
                    -> VarDepGraph
                    -> HM.HashMap Id Int
                    -> m VarDepGraph
addPortDependencies ModuleInstance{..} g varDepMap =
  HM.foldlWithKey'
  (\accG o qd ->
     let toNode v = hmGet 0 v varDepMap
         oVar = varName $ hmGet 1 o moduleInstancePorts
         oNode = toNode oVar
         fromNodes = fmap toNode . toList . getVariables . (\v -> hmGet 2 v moduleInstancePorts)
         accG' =
           foldl'
           (\g2 i -> insEdge (i, oNode, Implicit) g2)
           accG
           (concatMap fromNodes $ toList $ qd ^. implicitVars)
         accG'' =
           foldl'
           (\g2 i -> insEdge (i, oNode, Explicit) g2)
           accG'
           (concatMap fromNodes $ toList $ qd ^. explicitVars)
     in accG''
  ) g
  <$> asks (portDependencies . hmGet 3 moduleInstanceType)

mapLookup :: Show a => Int -> Id -> HM.HashMap Id a -> a
mapLookup n k m =
  case HM.lookup k m of
    Nothing ->
      error $ unlines [ "ModuleSummary.mapLookup: " ++ show n
                      , "map: " ++ show m
                      , "key:" ++ show k
                      ]
    Just a  -> a

type ThreadMap = IM.IntMap (Thread Int)
type GAD sig m = ( Has (Reader ModuleSummary) sig m
                 , Has (Reader ThreadMap) sig m
                 -- , Effect sig
                 )

-- | returns the transitive closure of the id of the threads that update the
-- given thread
getAllDependencies :: GAD sig m => Thread Int -> m IS.IntSet
getAllDependencies thread =
  execState mempty $
  asks ((`G.pre` getData thread) . threadDependencies)
  >>= traverse_ getAllDependencies'


getAllDependencies' :: (GAD sig m, Has (State IS.IntSet) sig m) => Int -> m ()
getAllDependencies' fromThreadId = do
  threadInSet <- gets (IS.member fromThreadId)
  unless threadInSet $ do
    modify (IS.insert fromThreadId)
    fromThread <- asks @ThreadMap (IM.! fromThreadId)
    unless (isAB fromThread) $
      asks ((`G.pre` fromThreadId) . threadDependencies)
      >>= traverse_ getAllDependencies'

type Ids3 = (Ids, Ids, Ids)

-- | returns the variables that are read from before written to in the given
-- statement
readBeforeWrittenTo :: AlwaysBlock Int -> Ids -> Ids
readBeforeWrittenTo ab initialWrittenVars = readBeforeWrittenSet
  -- -- | isStar ab = readBeforeWrittenSet
  -- -- | otherwise = error "this function should be called with a star block"
  where
    stmt = abStmt ab

    (_readSet, _writeSet, readBeforeWrittenSet) :: Ids3 =
      go stmt
      & execState (mempty, initialWrittenVars, mempty)
      & run

    go :: Has (State Ids3) sig m => Stmt Int -> m ()
    go Block{..} = traverse_ go blockStmts
    go Skip{}    = return ()

    go Assignment{..} = do
      newReadVars <- mappend (getVariables assignmentRhs) <$> use @Ids3 _1
      previouslyWrittenVars <- use @Ids3 _2
      let writtenVar = varName assignmentLhs
      when (writtenVar `notElem` previouslyWrittenVars &&
            writtenVar `elem` newReadVars) $
        modify @Ids3 $ _3 %~ HS.insert writtenVar
      modify @Ids3 $ _1 .~ newReadVars
      modify @Ids3 $ _2 %~ HS.insert writtenVar

    go IfStmt{..} = do
      oldWrittenVars <- use @Ids3 _2
      let condReadVars = getVariables ifStmtCondition
      readVars <- mappend condReadVars <$> use @Ids3 _1

      modify @Ids3 $ _1 .~ readVars
      go ifStmtThen
      readVarsThen    <- use @Ids3 _1
      writtenVarsThen <- use @Ids3 _2

      modify @Ids3 $ _1 .~ readVars
      modify @Ids3 $ _2 .~ oldWrittenVars
      go ifStmtElse
      readVarsElse    <- use @Ids3 _1
      writtenVarsElse <- use @Ids3 _2

      modify @Ids3 $ _1 .~ (readVarsThen <> readVarsElse)
      modify @Ids3 $ _2 .~ (writtenVarsThen <> writtenVarsElse)


instance Semigroup QualifierDependencies where
  qd1 <> qd2 =
    qd1 &
    (explicitVars %~ mappend (qd2 ^. explicitVars)) .
    (implicitVars %~ mappend (qd2 ^. implicitVars))


instance Monoid QualifierDependencies where
  mempty = QualifierDependencies mempty mempty

type Nodes = IS.IntSet
type NodeMap = IM.IntMap Id
type InvNodeMap = HM.HashMap Id Int
type QDMI  = IM.IntMap (Maybe QualifierDependencies)

moduleAnnots :: Module Int -> VarDepGraph -> NodeMap -> InvNodeMap -> PortDependencies
moduleAnnots m@Module{..} g nodeMap invNodeMap =
  foldl'
  (\acc o ->
     let n  = hmGet 5 o invNodeMap
         qd = case IM.lookup n qdmi of
                Nothing       -> error $ show o
                Just Nothing  -> mempty
                Just (Just a) -> a
         qd' = qd
               & (implicitVars %~ HS.intersection inputs)
               . (explicitVars %~ HS.intersection inputs)
     in HM.insert o qd' acc
  )
  mempty
  outputs
  where
    (sccG, _) = sccGraph g
    qdmi =
      run $ execState @QDMI mempty $ runReader m $ runReader g $ runReader nodeMap $
      for_ (G.topsort sccG) $ \sccN ->
      let (parentNodes, _, nodeSet, _) = G.context sccG sccN
      in if null parentNodes
         then for_ (IS.toList nodeSet) $
              \n -> modify @QDMI $ IM.insert n Nothing
         else moduleAnnotsSCC nodeSet & runReader nodeSet
    outputs = moduleOutputs m mempty
    inputs  = moduleInputs  m mempty

moduleAnnotsSCC :: ( Has (Reader (Module Int)) sig m
                   , Has (Reader VarDepGraph) sig m
                   , Has (Reader NodeMap) sig m
                   , Has (Reader Nodes) sig m
                   , Has (State QDMI) sig m
                   )
                => IS.IntSet
                -> m ()
moduleAnnotsSCC ns =
  if IS.null ns
  then return ()
  else do
    sccNodes <- ask @Nodes
    nodeMap <- ask @NodeMap
    g <- ask @VarDepGraph
    let toVar = (nodeMap IM.!)
    let currentNode = IS.findMin ns
        rest  = IS.delete currentNode ns
        getQD = gets . IM.findWithDefault (Just mempty)
    moldQD <- gets (IM.lookup currentNode)
    let oldQD = maybe mempty (fromMaybe mempty) moldQD
    newQD <-
      foldlM' oldQD (G.lpre g currentNode) $ \qd (parentNode, lbl) -> do
      let parentName = toVar parentNode
      mparentQD <- getQD parentNode
      return $
        case mparentQD of
          Nothing ->
            case lbl of
              Explicit -> qd & explicitVars %~ HS.insert parentName
              Implicit -> qd & implicitVars %~ HS.insert parentName
          Just parentQD ->
            case lbl of
              Explicit -> qd <> parentQD
              Implicit ->
                let parentQDVars =
                      (parentQD ^. implicitVars) <> (parentQD ^. explicitVars)
                in qd & implicitVars <>~ parentQDVars
    ns' <-
      if newQD /= oldQD || isNothing moldQD
      then do
        modify $ IM.insert currentNode (Just newQD)
        let newNodes =
              IS.fromList
              $ filter (`IS.member` sccNodes)
              $ G.suc g currentNode
        return $ rest <> newNodes
      else
        return rest
    moduleAnnotsSCC ns'

getVariableDependencies :: Id         -- ^ variable name
                        -> Module Int -- ^ module that contains the variable
                        -> SummaryMap -- ^ summary of all modules
                        -> [(Id, VarDepEdgeType)] -- ^ (written by an always block ?, variable name and dependency type pairs)
getVariableDependencies varName Module{..} summaryMap =
  if writtenByAB
  then first toName <$> G.lpre (variableDependencies moduleSummary) (toNode varName)
  else toVarDeps (portDeps ^. explicitVars) Explicit ++
       toVarDeps (portDeps ^. implicitVars) Implicit
  where
    toNode = (variableDependencyNodeMap moduleSummary HM.!)
    toName = (invVariableDependencyNodeMap moduleSummary IM.!)
    moduleSummary = summaryMap HM.! moduleName
    writeTid = threadWriteMap moduleSummary HM.! varName
    sameWriteTid :: GetData m => m Int -> Bool
    sameWriteTid = (== writeTid) . getData
    writtenByAB = any sameWriteTid alwaysBlocks

    mi = fromJust $ find sameWriteTid moduleInstances
    miSummary = summaryMap HM.! moduleInstanceType mi
    portName =
      fst $ fromJust $
      find (HS.member varName . getVariables . snd) $
      HM.toList (moduleInstancePorts mi)
    portDeps = portDependencies miSummary HM.! portName

    toVarDeps :: Ids -> VarDepEdgeType -> [(Id, VarDepEdgeType)]
    toVarDeps ps typ =
      let vs = mconcat $
               getVariables . (moduleInstancePorts mi HM.!) <$> HS.toList ps
      in (, typ) <$> HS.toList vs