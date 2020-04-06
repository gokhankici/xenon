{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}

module Iodine.Analyze.ModuleSummary
  (
    createModuleSummaries
  , getAllDependencies
  , ModuleSummary(..)
  , SummaryMap
  , readBeforeWrittenTo
  , QualifierDependencies
  , explicitVars
  , implicitVars
  )
where

import           Iodine.Analyze.DependencyGraph hiding (getNode)
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Lens
import           Control.Monad
import           Data.Foldable
import           Data.Maybe
import qualified Data.Graph.Inductive as G
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

data QualifierDependencies = QualifierDependencies
  { _explicitVars :: Ids
  , _implicitVars :: Ids
  }
  deriving (Eq)

makeLenses ''QualifierDependencies

type ModuleMap        = HM.HashMap Id (Module Int)
type TDGraph          = G.Gr () () -- ^ thread dependency graph
type Error            = PE.Error IodineException
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
                  threadWriteMap :: HM.HashMap Id IS.IntSet,

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
  deriving (Show)


-- #############################################################################

{- |
Create a summary for each given module
-}
createModuleSummaries :: Members '[ Reader AnnotationFile
                                  , PT.Trace
                                  , Error ] r
                      => L (Module Int) -- ^ modules (filtered & topologically sorted)
                      -> ModuleMap      -- ^ same modules, in a hash map
                      -> Sem r SummaryMap
createModuleSummaries orderedModules moduleMap =
  -- trace "ordered modules" (moduleName <$> orderedModules)
  for_ orderedModules (\m@Module{..} ->
                          createModuleSummary m >>= (modify . HM.insert moduleName))
    & runReader moduleMap
    & runState @SummaryMap mempty
    & fmap fst


createModuleSummary :: Members '[ Reader AnnotationFile
                                , State SummaryMap
                                , PT.Trace
                                , Error
                                , Reader ModuleMap
                                ] r
                    => Module Int
                    -> Sem r ModuleSummary
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

  let nodeMap = IM.fromList $ swap <$> HM.toList varDepMap
  varDepGraph' <-
    foldlM' varDepGraph moduleInstances $ \g ModuleInstance{..} ->
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
    <$> gets (portDependencies . hmGet 3 moduleInstanceType)

  portDeps <- moduleAnnots m varDepGraph' nodeMap varDepMap

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
          <$> asks (hmGet 4 moduleInstanceType)
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
    , threadWriteMap               = dgState ^. varUpdates
    , variableDependencies         = varDepGraph
    , variableDependencyNodeMap    = varDepMap
    , invVariableDependencyNodeMap = nodeMap
    , variableDependenciesSCC      = sccG
    , variableDependencySCCNodeMap = toSCCNodeMap
    }
  where
    swap (a,b) = (b,a)
    inputsSet = moduleInputs m mempty


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

-- | returns the variables that are read from before written to in the given
-- statement
readBeforeWrittenTo :: AlwaysBlock Int -> Ids -> Ids
readBeforeWrittenTo ab initialWrittenVars = readBeforeWrittenSet
  -- -- | isStar ab = readBeforeWrittenSet
  -- -- | otherwise = error "this function should be called with a star block"
  where
    stmt = abStmt ab

    (_readSet, _writeSet, readBeforeWrittenSet) =
      go stmt
      & execState (mempty, initialWrittenVars, mempty)
      & run

    go :: Members '[State (Ids, Ids, Ids)] r => Stmt Int -> Sem r ()
    go Block{..} = traverse_ go blockStmts
    go Skip{}    = return ()

    go Assignment{..} = do
      newReadVars <- mappend (getVariables assignmentRhs) <$> gets (view _1)
      previouslyWrittenVars <- gets (view _2)
      let writtenVar = varName assignmentLhs
      when (writtenVar `notElem` previouslyWrittenVars &&
            writtenVar `elem` newReadVars) $
        modify $ _3 %~ HS.insert writtenVar
      modify $ _1 .~ newReadVars
      modify $ _2 %~ HS.insert writtenVar

    go IfStmt{..} = do
      oldWrittenVars <- gets (view _2)
      let condReadVars = getVariables ifStmtCondition
      readVars <- mappend condReadVars <$> gets (view _1)

      modify $ _1 .~ readVars
      go ifStmtThen
      readVarsThen   <- gets (view _1)
      writtenVarsThen <- gets (view _2)

      modify $ _1 .~ readVars
      modify $ _2 .~ oldWrittenVars
      go ifStmtElse
      readVarsElse    <- gets (view _1)
      writtenVarsElse <- gets (view _2)

      modify $ _1 .~ (readVarsThen <> readVarsElse)
      modify $ _2 .~ (writtenVarsThen <> writtenVarsElse)


instance Semigroup QualifierDependencies where
  qd1 <> qd2 =
    qd1 &
    (explicitVars %~ mappend (qd2 ^. explicitVars)) .
    (implicitVars %~ mappend (qd2 ^. implicitVars))


instance Monoid QualifierDependencies where
  mempty = QualifierDependencies mempty mempty

instance Show QualifierDependencies where
  show qd = "{ explicit: " ++ show (toList $ qd ^. explicitVars) ++
            ", implicit: " ++ show (toList $ qd ^. implicitVars) ++
            "}"

type Nodes = IS.IntSet
type NodeMap = IM.IntMap Id
type InvNodeMap = HM.HashMap Id Int
type QDMI  = IM.IntMap (Maybe QualifierDependencies)

moduleAnnots :: Module Int -> VarDepGraph -> NodeMap -> InvNodeMap -> Sem r PortDependencies
moduleAnnots m@Module{..} g nodeMap invNodeMap = do
  let (sccG, _) = sccGraph g
  qdmi <-
    execState @QDMI mempty $ runReader m $ runReader g $ runReader nodeMap $
    for_ (G.topsort sccG) $ \sccN ->
    let (parentNodes, _, nodeSet, _) = G.context sccG sccN
    in if null parentNodes
       then for_ (IS.toList nodeSet) $
            \n -> modify $ IM.insert n Nothing
       else moduleAnnotsSCC nodeSet & runReader nodeSet
  let outputs = moduleOutputs m mempty
      inputs  = moduleInputs  m mempty
  return $
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

moduleAnnotsSCC :: Members '[ Reader (Module Int)
                            , Reader VarDepGraph
                            , Reader NodeMap
                            , Reader Nodes
                            , State QDMI
                            ] r
                => IS.IntSet
                -> Sem r ()
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
