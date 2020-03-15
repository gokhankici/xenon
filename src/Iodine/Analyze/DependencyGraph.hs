{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
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

type ModuleMap   = HM.HashMap Id (Module Int)
type VarDepGraph = Gr () VarDepEdgeType
data VarDepEdgeType = Implicit | Explicit AssignmentType deriving (Show)
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
dependencyGraph :: Members '[Reader ModuleMap, Reader AnnotationFile] r
                =>  Module Int -> Sem r DependencyGraphSt
dependencyGraph Module{..} = execState initialState $ do
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
              modify (threadGraph %~ G.insEdge (writeThread, readThread, ()))
          )
    ) vrs
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

dependencyGraphActMI :: Members '[ Reader ModuleMap
                                 , Reader AnnotationFile
                                 , State DependencyGraphSt] r
                     => ModuleInstance Int
                     -> Sem r ()
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

lookupThreads :: Member (State DependencyGraphSt) r
              => Id
              -> Getter DependencyGraphSt (HM.HashMap Id Ints)
              -> Sem r [Int]
lookupThreads v optic =
  gets (concatMap IS.toList . HM.lookup v . (^. optic))

dependencyGraphActAB :: Member (State DependencyGraphSt) r
                     => AlwaysBlock Int -> Sem r ()
dependencyGraphActAB ab = do
  modify (threadGraph %~ G.insNode (getData ab, ()))
  runReader (getData ab) $ handleStmt (abStmt ab)

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
  oldPathVars <- gets (view pathVars)
  let condVars = getVariables ifStmtCondition
  tid <- ask
  for_ condVars $ \condVar -> modify (varReads %~ addToSet condVar tid)
  newPathVars <- getNodes condVars
  modify $ pathVars %~ IS.union newPathVars
  traverse_ handleStmt [ifStmtThen, ifStmtElse]
  modify $ pathVars .~ oldPathVars

type DGSt r = Members '[State DependencyGraphSt] r

addNode :: DGSt r => (Int, Int, VarDepEdgeType) -> Sem r ()
addNode edge@(fromNode, toNode, _) = do
  for_ [fromNode, toNode] $ \n ->
    modify $ depGraph %~ G.insNode (n, ())
  modify $ depGraph %~ G.insEdge edge


getNodes :: DGSt r => HS.HashSet Id -> Sem r IS.IntSet
getNodes = fmap IS.fromList . traverse getNode . HS.toList


getNode :: DGSt r => Id -> Sem r Int
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
