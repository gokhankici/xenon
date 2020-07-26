{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Iodine.Transform.Merge (merge) where

import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.State.Strict
import           Control.Effect.Error
import           Control.Effect.Reader
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive.Dot as GD
import           Data.Graph.Inductive.PatriciaTree (Gr)
import qualified Data.Graph.Inductive.Query as GQ
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Sequence as SQ
import           Control.Effect.Lift
import           Data.List (sortOn)

type A = Int
type DepGraph = Gr Int ()
type StmtMap  = IM.IntMap (Stmt A)
data St =
  St { _writtenBy   :: HM.HashMap Id IS.IntSet
     , _readBy      :: HM.HashMap Id IS.IntSet
     , _stmtCounter :: Int
     , _stmtMap     :: StmtMap
     }

makeLenses ''St

type OldG sig m = ( Has (Reader AnnotationFile) sig m
                  , Has (Reader ModuleMap) sig m
                  , Has (Error IodineException) sig m
                  , Has (Lift IO) sig m
                  )
type G sig m = (OldG sig m, Has (State Int) sig m)

-- -----------------------------------------------------------------------------
merge :: OldG sig m => L (Module A) -> m (L (Module A))
-- -----------------------------------------------------------------------------
merge modules = evalState (getMaxThreadId modules + 1) $
                traverse mergeModule modules

-- | make gate statements a always* block, and merge with the rest
-- assumes that module id is greater than the ids of its thread
mergeModule :: G sig m => Module A -> m (Module A)
mergeModule Module {..} = do
  gateBlocks <- traverse  makeStarBlock gateStmts
  alwaysBlocks' <- mergeAlwaysBlocks $ alwaysBlocks <> gateBlocks
  return $
    Module { gateStmts    = mempty
           , alwaysBlocks = alwaysBlocks'
           , ..
           }

{- |
All blocks with the same non-star event are merged into a single block (with
random ordering). For the always* blocks, a dependency graph is created first
and then they are merged according to their order in the directed-acyclic graph.
-}
mergeAlwaysBlocks :: G sig m => L (AlwaysBlock A) -> m (L (AlwaysBlock A))
mergeAlwaysBlocks as =
  foldlM' mempty (HM.toList eventMap) $ \acc (e, eAs) -> do
    ab' <-
      case e of
        Star -> mergeAlwaysStarBlocks eAs
        _    -> return $ mergeAlwaysEventBlocks e eAs
    return $ acc |> ab'
  where
    eventMap = foldl' updateM mempty as
    updateM m ab@AlwaysBlock{..} = HM.alter (append (SQ.<|) ab) abEvent m


{- |
Merge every always* block into a single one. The statements that belong to the
same connected components are ordered according to their topological sort.
However, the order between connected components are random.
-}
mergeAlwaysStarBlocks :: G sig m => L (AlwaysBlock A) -> m (AlwaysBlock A)
mergeAlwaysStarBlocks as = do
  (depGraph, stmtIds) <- buildDependencyGraph (abStmt <$> as)
  unless (G.noNodes depGraph == SQ.length as) $
    throwError . IE Merge  $ "graph size does not match up with the initial statements"
  let components = G.components depGraph
      graphs = (\ns -> G.nfilter (`elem` ns) depGraph) <$> components
  stmts' <- foldlM' mempty graphs $ \acc g -> do
    let stmtOrder = GQ.topsort g
    when (hasCycle g) $ do
      let cycleNodes = snd $
                       head $
                       sortOn fst $
                       (\l -> (length l, l)) <$>
                       filter (\l -> length l > 1) (GQ.scc g)
          g' = G.nfilter (`elem` cycleNodes) g
          dotStr = GD.showDot $ GD.fglToDotString $ G.nemap show (const "") g'
          sep = replicate 80 '-'
      sendIO $ do writeFile "merge-cycle.dot" dotStr
                  for_ cycleNodes $ \n -> do
                    putStrLn sep
                    putStrLn $ "stmt " <> show n
                    putStrLn sep
                    putStrLn $ prettyShow $ stmtIds IM.! n
                    putStrLn ""
      throwError $ IE Merge "star dependency graph has a loop"
    return $ (stmtIds IM.!) <$> stmtOrder
             & SQ.fromList
             & (acc <>)
  makeStarBlock (Block stmts' emptyStmtData)

{- |
merge the always blocks with the same non-star event after makign sure that
their dependecy graph form a DAG
-}
mergeAlwaysEventBlocks :: Event A -> L (AlwaysBlock A) -> AlwaysBlock A
mergeAlwaysEventBlocks e as = AlwaysBlock e stmt' (getFirstData as)
  where
    stmts = abStmt <$> as
    stmt' =
      case stmts of
        SQ.Empty          -> error "this should be unreachable"
        s SQ.:<| SQ.Empty -> s
        _                 -> Block stmts emptyStmtData

type ModuleMap = HM.HashMap Id (Module A)
type FD sig m = (Has (State St) sig m, Has (Reader ModuleMap) sig m)

{- |
builds a dependency graph where (s1, s2) \in G iff there exists a variable v
such that s1 updates v and s2 reads v
-}
buildDependencyGraph :: (Has (Reader ModuleMap) sig m) -- , Effect sig)
                     => L (Stmt A) -> m (DepGraph, StmtMap)
buildDependencyGraph stmts =
  traverse_ update stmts
  & runState initialState
  & fmap (\(st, _) -> ( buildGraph (st ^. readBy) (st ^. writtenBy) (st ^. stmtMap & IM.keysSet)
                      , st ^. stmtMap
                      ))
  where
    buildGraph readMap writeMap nodes =
      HM.foldlWithKey'
      (\g v fromIds ->
         case HM.lookup v readMap of
           Nothing    -> g
           Just toIds ->
             IS.foldl'
             (\g2 fromId ->
                IS.foldr'
                (\toId -> G.insEdge (fromId, toId, ()))
                g2
                toIds
             )
             g
             fromIds
      )
      (IS.foldr' (\n -> G.insNode (n, n)) G.empty nodes)
      writeMap

    -- create a new id for the given statement, and update its read & write set
    update :: FD sig m => Stmt A -> m ()
    update s = do
      n <- gets (^. stmtCounter)
      modify $
        (stmtCounter +~ 1) .
        (stmtMap . at n ?~ s)
      updateN n s

    -- update read & write sets for the given statement id
    updateN :: FD sig m => Int -> Stmt A -> m ()
    updateN n Block {..} = traverse_ (updateN n) blockStmts
    updateN n Assignment {..} = do
      forM_ (getVariables assignmentLhs) (insertToWrites n)
      forM_ (getVariables assignmentRhs) (insertToReads n)
    updateN n IfStmt   {..} = do
      forM_ (getVariables ifStmtCondition) (insertToReads n)
      updateN n ifStmtThen
      updateN n ifStmtElse
    updateN _ Skip {..} = return ()

    insertToWrites n v =
      modify $ writtenBy %~ HM.alter (append IS.insert n) v

    insertToReads n v =
      modify $ readBy %~ HM.alter (append IS.insert n) v

initialState :: St
initialState = St mempty mempty 0 mempty

makeStarBlock :: G sig m => Stmt A -> m (AlwaysBlock A)
makeStarBlock stmts = AlwaysBlock Star stmts <$> getFreshId

{- |
given a updater function and an element, create a helper function to be used
with `HM.alter`
-}
append :: Monoid m => (a -> m -> m) -> a -> Maybe m -> Maybe m
append f a = \case
  Nothing -> Just $ f a mempty
  Just m  -> Just $ f a m

{- |
if a graph does not have a cycle, each strongly connected component of the graph
should consist of a single element
-}
hasCycle :: DepGraph -> Bool
hasCycle g = length (GQ.scc g) /= G.noNodes g

emptyStmtData :: A
emptyStmtData = 0

getFirstData :: L (AlwaysBlock a) -> a
getFirstData (ab SQ.:<| _) = getData ab
getFirstData _ = undefined

getFreshId :: G sig m => m Int
getFreshId = get <* modify @Int (+ 1)

getMaxThreadId :: Ord a => L (Module a) -> a
getMaxThreadId = maximum . fmap goM
  where
    goM m@Module{..} =
      maximum $
      getData m
      <| (getData <$> alwaysBlocks)
      <> (getData <$> moduleInstances)
