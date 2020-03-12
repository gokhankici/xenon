{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Analyze.DependencyGraph
  ( dependencyGraph
  , VarDepGraph
  , VarDepEdgeType(..)
  , ThreadDepGraph
  , depGraph
  , pathVars
  , varMap
  , varCounter
  , varReads
  , varUpdates
  , threadGraph
  )
where

import           Iodine.Language.IR
import           Iodine.Types

import           Control.Lens
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import           Data.Graph.Inductive.PatriciaTree (Gr)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntSet as IS
import           Polysemy
import           Polysemy.State
import           Polysemy.Reader

type VarDepGraph = Gr () VarDepEdgeType
data VarDepEdgeType = Implicit | Explicit AssignmentType
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
dependencyGraph :: Foldable t => t (AlwaysBlock Int) -> DependencyGraphSt
dependencyGraph threads = for_ threads dependencyGraphAct
                          & execState initialState & run
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

dependencyGraphAct :: AlwaysBlock Int -> Sem '[State DependencyGraphSt] ()
dependencyGraphAct ab = do
  runReader (getData ab) $ handleStmt (abStmt ab)
  gets (HM.toList . (^. varUpdates))
    >>= traverse_ (
    \(writtenVar, writtenThreads) -> do
      mReadThreads <- gets (HM.lookup writtenVar . (^. varReads))
      case mReadThreads of
        Nothing -> return ()
        Just readThreads ->
          for_ (IS.toList writtenThreads) $ \wt ->
          for_ (IS.toList readThreads) $ \rt ->
          modify (threadGraph %~ (G.insEdge (wt, rt, ()) . G.insNode (rt, ()) . G.insNode (wt, ())))
    )

type FD r = Members '[State DependencyGraphSt, Reader Int] r

handleStmt :: FD r => Stmt a -> Sem r ()
handleStmt Skip{..}  = return ()
handleStmt Block{..} = traverse_ handleStmt blockStmts
handleStmt Assignment{..} =
  case assignmentLhs of
    Variable{..} -> do
      lhsNode <- getNode varName
      let rhsVars = getVariables assignmentRhs
      rhsNodes <- getNodes rhsVars
      for_ (IS.toList rhsNodes) $ \rhsNode ->
        addNode (rhsNode, lhsNode, Explicit assignmentType)
      pathNodes <- gets (^. pathVars)
      for_ (IS.toList pathNodes) $ \pathNode ->
        addNode (pathNode, lhsNode, Implicit)
      -- update the thread map
      tid <- ask
      modify (varUpdates %~ addToSet varName tid)
      for_ rhsVars $ \rhsVar -> modify (varReads %~ addToSet rhsVar tid)
    _ -> error "assignment lhs is non-variable"
handleStmt IfStmt{..} = do
  currentSt <- get
  newPathVars <- getNodes (getVariables ifStmtCondition)
  modify $ pathVars %~ IS.union newPathVars
  traverse_ handleStmt [ifStmtThen, ifStmtElse]
  modify $ pathVars .~ (currentSt ^. pathVars)

addNode :: FD r => (Int, Int, VarDepEdgeType) -> Sem r ()
addNode edge@(fromNode, toNode, _) = do
  for_ [fromNode, toNode] $ \n ->
    modify $ depGraph %~ G.insNode (n, ())
  modify $ depGraph %~ G.insEdge edge


getNodes :: FD r => HS.HashSet Id -> Sem r IS.IntSet
getNodes = fmap IS.fromList . traverse getNode . HS.toList


getNode :: FD r => Id -> Sem r Int
getNode v = do
  res <- gets (^. varMap . to (HM.lookup v))
  case res of
    Nothing -> do
      n <- gets (^. varCounter)
      modify $
        (varCounter +~ 1) .
        (varMap %~ HM.insert v n)
      return n
    Just n -> return n

addToSet :: Id -> Int -> HM.HashMap Id Ints -> HM.HashMap Id Ints
addToSet k i = HM.alter upd k
  where
    upd Nothing   = Just $ IS.singleton i
    upd (Just is) = Just $ IS.insert i is
