{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module Iodine.Utils where

import           Iodine.Types

import           Control.Applicative
import           Control.Effect.Error
import qualified Control.Effect.Trace as EF
import           Control.Effect.Writer
import           Control.Lens
import           Control.Monad
import qualified Data.DList as DL
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Hashable
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import           Data.Maybe
import qualified Data.Sequence as SQ
import           Text.Printf

combine :: (Monad f, Monoid m, Traversable t) => (a -> f m) -> t a -> f m
combine act as = fold <$> traverse act as

mfold :: (Foldable f, Monoid m) => (a -> m) -> f a -> m
mfold f = foldl' (\ms a -> f a <> ms) mempty

mfoldM :: (Foldable f, Monoid o, Monad m) => (a -> m o) -> f a -> m o
mfoldM f as = foldlM' mempty as $ \acc a -> mappend acc <$> f a

intersects :: HS.HashSet Id -> HS.HashSet Id -> Bool
intersects s1 s2 = go (HS.toList s1)
 where
  go []       = False
  go (a : as) = HS.member a s2 || go as

notSupported :: a
notSupported = error "not supported"

infixl 9 ||>
(||>) :: Applicative f => f (L a) -> f a -> f (L a)
(||>) fas fa = (|>) <$> fas <*> fa

infixl 9 <||>
(<||>) :: Applicative f => f (L a) -> f (L a) -> f (L a)
(<||>) = liftA2 (<>)

(|:>) :: (Snoc s s a a, Monoid s) => a -> a -> s
(|:>) a1 a2 = mempty |> a1 |> a2

uncurry2 :: (a -> b -> c) -> (a, b) -> c
uncurry2 f (a, b) = f a b

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

curry2 :: ((a, b) -> c) -> (a -> b -> c)
curry2 f a b = f (a, b)

curry3 ::((a, b, c) -> d) -> (a -> b -> c -> d)
curry3 f a b c = f (a, b, c)

foldlM' :: (Foldable t, Monad m)
       => b -> t a -> (b -> a -> m b) -> m b
foldlM' b as act = foldlM act b as

class Monoid (m a) => LiftToMonoid m a where
  liftToMonoid :: a -> m a

instance LiftToMonoid SQ.Seq a where
  liftToMonoid = SQ.singleton

instance LiftToMonoid [] a where
  liftToMonoid = (: [])

instance (Hashable a, Eq a) => LiftToMonoid HS.HashSet a where
  liftToMonoid = HS.singleton

maybeToMonoid :: LiftToMonoid m a => Maybe a -> m a
maybeToMonoid (Just a) = liftToMonoid a
maybeToMonoid Nothing  = mempty

catMaybes' :: (Foldable t, LiftToMonoid t a) => t (Maybe a) -> t a
catMaybes' = foldl' (\acc -> maybe acc (mappend acc . liftToMonoid)) mempty

toSequence :: Foldable t => t a -> L a
toSequence = foldl' (|>) mempty

toHSet :: (Eq a, Hashable a, Foldable t) => t a -> HS.HashSet a
toHSet = foldl' (flip HS.insert) mempty

-- | return combinations of the elements
twoPairs :: L a -> L (a, a)
twoPairs SQ.Empty      = mempty
twoPairs (a SQ.:<| as) = ((a, ) <$> as) <> twoPairs as

-- >>> twoPairs $ SQ.fromList [1..4]
-- fromList [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

insEdge :: (Eq b, G.DynGraph gr) => G.LEdge b -> gr a b -> gr a b
insEdge e g =
  if G.hasLEdge g e
  then g
  else G.insEdge e g

find' :: (Foldable t, Show a) => (a -> Bool) -> t a -> a
find' q as =
  case find q as of
    Just a  -> a
    Nothing -> error $ "Could not find matching element in " ++ show (toList as)

printGraph :: Show b => G.Gr a b -> (Int -> String) -> String
printGraph g nodeLookup = unlines ls
  where
    ls = "digraph iodine {" : edges ++ nodes ++ ["}"]
    edges = mkEdge <$> G.labEdges g
    nodes = mkNode <$> G.nodes g
    mkEdge (x,y,b) = printf "%d -> %d [label=\"%s\"];" x y (show b)
    mkNode n = printf "%d [label=\"%s\"];" n (nodeLookup n)

hmGet :: (Show k, Show v, Eq k, Hashable k)
      => Int -> k -> HM.HashMap k v -> v
hmGet n k m =
  case HM.lookup k m of
    Nothing ->
      error $ unlines [ "hashmap"
                      , show m
                      , "key " ++ show k
                      , "no " ++ show n
                      ]
    Just v -> v

-- >>> hmGetEmpty "2" $ HM.fromList [("1", [1]), ("2", [2])]
-- [2]
-- >>> hmGetEmpty "20" $ HM.fromList [("1", [1]), ("2", [2])]
-- []
hmGetEmpty :: (Eq k, Hashable k, Monoid v) => k -> HM.HashMap k v -> v
hmGetEmpty k m = fromMaybe mempty $ HM.lookup k m

-- >>> mkMap show [1..10]
-- fromList [("7",7),("1",1),("10",10),("4",4),("5",5),("2",2),("3",3),("8",8),("9",9),("6",6)]
mkMap :: (Foldable t, Hashable k, Eq k)
      => (a -> k)
      -> t a
      -> HM.HashMap k a
mkMap toKey = foldl' (\acc a -> HM.insert (toKey a) a acc) mempty


-- | Creates a scc graph where the each node corresponds to a strongly connected
-- component of the original graph. There's an edge between scc_i & scc_j if
-- there was an edge (u,v) in the original graph where (u \in scc_i) and (v \in
-- scc_j). The new graph does not contain any loop, including self loops. In the
-- new graph, node labels are the set of nodes that form the corresponding scc.
sccGraph :: Eq b
         => G.Gr a b
         -> (G.Gr IS.IntSet b, IM.IntMap Int)
sccGraph g = (g2, toSCCNodeMap)
  where
    g2 =
      foldl'
      (\acc_g (n1, n2, b) ->
         let n1' = toSCCNode n1
             n2' = toSCCNode n2
         in if n1' /= n2'
            then insEdge (n1', n2', b) acc_g
            else acc_g)
      g1 (G.labEdges g)
    toSCCNode = (toSCCNodeMap IM.!)
    (g1, toSCCNodeMap) =
      foldl' update (G.empty, IM.empty) (G.scc g)
    update (acc_g, acc_m) = \case
      scc@(sccNode:_) ->
        let g'  = G.insNode (sccNode, IS.fromList scc) acc_g
            m'  = foldl' (\m n -> IM.insert n sccNode m) acc_m scc
        in (g', m')
      [] -> error "unreachable"

assert :: Has (Error IodineException) sig m
       => Bool -> String -> m ()
assert check msg =
  unless check $ throwError (IE Assert msg)

trace :: (Has EF.Trace sig m, Show a) => String -> a -> m ()
trace msg a = do
  EF.trace msg
  EF.trace $ show a
  EF.trace ""

output :: Has (Writer Output) sig m => [String] -> m ()
output = tell . DL.fromList
