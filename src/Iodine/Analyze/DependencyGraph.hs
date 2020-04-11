{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Analyze.DependencyGraph
  ( dependencyGraph
  , DependencyGraphSt
  , depGraph
  , pathVars
  , varMap
  , varCounter
  , varReads
  , varUpdates
  , threadGraph
  , VarDepGraph
  , VarDepEdgeType(..)
  )
where

import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Lens
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import           Data.Graph.Inductive.PatriciaTree (Gr)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntSet as IS

type ModuleMap   = HM.HashMap Id (Module Int)
type VarDepGraph = Gr () VarDepEdgeType
data VarDepEdgeType = Implicit | Explicit deriving (Show, Eq, Read)
type Ints = IS.IntSet
type ThreadDepGraph = Gr () ()

data DependencyGraphSt =
  DependencyGraphSt
  { _depGraph    :: VarDepGraph        -- ^ variable dependency map
  , _pathVars    :: Ints               -- ^ path variables
  , _varMap      :: HM.HashMap Id Int  -- ^ variable name -> node id
  , _varCounter  :: Int                -- ^ for creating fresh node ids
  , _varReads    :: HM.HashMap Id Ints -- ^ thread ids that read a variable
  , _varUpdates  :: HM.HashMap Id Ints -- ^ thread ids that update a variable
  , _threadGraph :: ThreadDepGraph     -- ^ thread dependency graph
  }

makeLenses ''DependencyGraphSt


{- |
Creates a dependency graph for the variables that occur inside the given
statement.

- (v1, v2, Explicit) \in E iff v1's value directly affects the value of v2

- (v1, v2, Implicit) \in E iff v1 is a path variable (occurs inside the
  condition of an if statement where v2 is assigned)
-}
dependencyGraph :: ( Has (Reader ModuleMap) sig m
                   , Has (Reader AnnotationFile) sig m
                   , Effect sig
                   )
                =>  Module Int -> m DependencyGraphSt
dependencyGraph = fmap fst . runState initialState . dependencyGraphHelper
  where
    initialState =
      DependencyGraphSt
      { _depGraph    = G.empty
      , _pathVars    = mempty
      , _varMap      = mempty
      , _varCounter  = 0
      , _varReads    = mempty
      , _varUpdates  = mempty
      , _threadGraph = G.empty
      }

dependencyGraphHelper :: ( Has (Reader ModuleMap) sig m
                         , Has (Reader AnnotationFile) sig m
                         , Has (State DependencyGraphSt) sig m
                         )
                      =>  Module Int -> m ()
dependencyGraphHelper Module{..} = do
  for_ variables (getNode . variableName)
  for_ alwaysBlocks dependencyGraphActAB
  for_ moduleInstances dependencyGraphActMI
  vrs :: HM.HashMap Id Ints <- gets (view varReads)
  HM.traverseWithKey
    (\readVar readThreads -> do
        writeThreads <- lookupThreads readVar varUpdates
        for_ writeThreads
          (\writeThread ->
              for_ (IS.toList readThreads) $ \readThread ->
              modify (threadGraph %~ insEdge (writeThread, readThread, ()))
          )
    ) vrs
  return ()

dependencyGraphActMI :: ( Has (Reader ModuleMap) sig m
                        , Has (Reader AnnotationFile) sig m
                        , Has (State DependencyGraphSt) sig m
                        )
                     => ModuleInstance Int
                     -> m ()
dependencyGraphActMI mi@ModuleInstance{..} = do
  let miThreadId = getData mi
  modify (threadGraph %~ G.insNode (miThreadId, ()))
  (miReads, miWrites) <-
    moduleInstanceReadsAndWrites
    <$> asks (HM.! moduleInstanceType)
    <*> getClocks moduleInstanceType
    <*> return mi
  for_ miReads $ \readVar ->
    modify (varReads %~ addToSet readVar miThreadId)
  for_ miWrites $ \writtenVar ->
    modify (varUpdates %~ addToSet writtenVar miThreadId)

lookupThreads :: Has (State DependencyGraphSt) sig m
              => Id
              -> Getter DependencyGraphSt (HM.HashMap Id Ints)
              -> m [Int]
lookupThreads v optic =
  gets (concatMap IS.toList . HM.lookup v . (^. optic))

dependencyGraphActAB :: Has (State DependencyGraphSt) sig m
                     => AlwaysBlock Int -> m ()
dependencyGraphActAB ab = do
  modify (threadGraph %~ G.insNode (getData ab, ()))
  runReader (getData ab) $ handleStmt (abStmt ab)

type FD sig m = (Has (State DependencyGraphSt) sig m, Has (Reader Int) sig m)

handleStmt :: FD sig m => Stmt a -> m ()
handleStmt Skip{..}  = return ()
handleStmt Block{..} = traverse_ handleStmt blockStmts
handleStmt Assignment{..} =
  case assignmentLhs of
    Variable{..} -> do
      lhsNode <- getNode varName
      let rhsVars = getVariables assignmentRhs
      rhsNodes <- getNodes rhsVars
      for_ (IS.toList rhsNodes) $ \rhsNode ->
        addEdge (rhsNode, lhsNode, Explicit)
      pathNodes <- gets (^. pathVars)
      for_ (IS.toList pathNodes) $ \pathNode ->
        addEdge (pathNode, lhsNode, Implicit)
      -- update the thread map
      tid <- ask
      modify (varUpdates %~ addToSet varName tid)
      for_ rhsVars $ \rhsVar -> modify (varReads %~ addToSet rhsVar tid)
    _ -> error "assignment lhs is non-variable"
handleStmt IfStmt{..} = do
  oldPathVars <- gets (view pathVars)
  let condVars = getVariables ifStmtCondition
  tid <- ask
  for_ condVars $ \condVar -> modify (varReads %~ addToSet condVar tid)
  newPathVars <- getNodes condVars
  modify $ pathVars %~ IS.union newPathVars
  traverse_ handleStmt [ifStmtThen, ifStmtElse]
  modify $ pathVars .~ oldPathVars

type DGSt sig m = Has (State DependencyGraphSt) sig m

addEdge :: DGSt sig m => (Int, Int, VarDepEdgeType) -> m ()
addEdge edge = modify $ depGraph %~ insEdge edge

getNodes :: DGSt sig m => HS.HashSet Id -> m IS.IntSet
getNodes = fmap IS.fromList . traverse getNode . HS.toList

getNode :: DGSt sig m => Id -> m Int
getNode v = do
  res <- gets (^. varMap . to (HM.lookup v))
  case res of
    Nothing -> do
      n <- gets (^. varCounter)
      modify $
        (varCounter +~ 1) .
        (varMap %~ HM.insert v n) .
        (depGraph %~ G.insNode (n, ()))
      return n
    Just n -> return n

addToSet :: Id -> Int -> HM.HashMap Id Ints -> HM.HashMap Id Ints
addToSet k i = HM.alter upd k
  where
    upd Nothing   = Just $ IS.singleton i
    upd (Just is) = Just $ IS.insert i is
