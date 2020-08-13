{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module Iodine.Utils
  ( combine, mfold, mfoldM, intersects, notSupported, (||>), (<||>), (|:>)
  , uncurry3, curry3
  , maybeToMonoid, catMaybes', toSequence
  , toHSet, twoPairs, insEdge, find', hmGet, hmGetEmpty, mkMap, sccGraph
  , assert, trace, output, groupSort, swap, nub', toDotStr, foldlM'
  , silence
  ) where

import           Iodine.Types

import           Control.Applicative
import           Control.Effect.Error
import qualified Control.Effect.Trace as EF
import           Control.Effect.Writer
import           Control.Exception (bracket)
import           Control.Lens
import           Control.Monad
import qualified Data.DList as DL
import           Data.Foldable
import           Data.List
import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive.Dot as GD
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Hashable
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import           Data.Maybe
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Text.Read (readMaybe)
import           GHC.IO.Handle
import           System.IO

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

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

curry3 ::((a, b, c) -> d) -> (a -> b -> c -> d)
curry3 f a b c = f (a, b, c)

foldlM' :: (Foldable t, Monad m)
       => b -> t a -> (b -> a -> m b) -> m b
foldlM' b as act = foldlM act b as

class Monoid (m a) => LiftToMonoid m a where
  toMonoid :: a -> m a

instance (Hashable a, Eq a) => LiftToMonoid HS.HashSet a where
  toMonoid = HS.singleton

instance (Monad m, Monoid (m a)) => LiftToMonoid m a where
  toMonoid = return

maybeToMonoid :: LiftToMonoid m a => Maybe a -> m a
maybeToMonoid = maybe mempty toMonoid

catMaybes' :: (Foldable t, LiftToMonoid t a) => t (Maybe a) -> t a
catMaybes' = foldl' (\acc -> maybe acc (mappend acc . toMonoid)) mempty

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

groupSort :: Ord a => [(a, b)] -> [(a, [b])]
groupSort = fmap go . groupBy (\(a1,_) (a2, _) -> a1 == a2) . sortOn fst
  where go []           = undefined
        go ((a,b):rest) = (a, b:(snd <$> rest))

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

nub' :: (Eq b, Hashable b) => (a -> b) ->  [a] -> [a]
nub' f xs = snd $ foldr' go (HS.empty, []) xs
  where go x (hist, xs') =
          if   HS.member (f x) hist
          then (hist, xs')
          else (HS.insert (f x) hist, x : xs')

newtype GraphNode a = GraphNode { getGraphNode :: a } deriving (Show, Read)
newtype GraphEdge b = GraphEdge { getGraphEdge :: b } deriving (Show, Read)

toDotStr :: ( G.DynGraph gr
            , Show a, Read a
            , Show b, Read b
            )
         => (G.Node -> Id) -- ^ convert node number to text
         -> (a -> String)  -- ^ convert node label to text
         -> (b -> String)  -- ^ edge style
         -> gr a b
         -> String
toDotStr nodeConv nodeLabelConv edgeStyle g =
  GD.showDot $ GD.fglToDotGeneric (fixG g) show show attrConv
  where
    toNodeLabel, toEdgeLabel :: String -> Maybe [(String, String)]
    toNodeLabel lbl = do
      (n, a) <- getGraphNode <$> readMaybe lbl
      Just [("label", T.unpack (nodeConv n) <> nodeLabelConv a)]
    toEdgeLabel lbl = do
      lbl' <- getGraphEdge <$> readMaybe lbl
      Just [("style", edgeStyle lbl')]

    attrConv = \case
      [("label", lbl)] -> fromJust $ toNodeLabel lbl <|> toEdgeLabel lbl
      _                -> error "unreachable"

    fixG = G.emap GraphEdge .
           G.gmap (\(ps, n, a, ss) -> (ps, n, GraphNode (n, a), ss))

silence :: IO a -> IO a
silence action = withFile "/dev/null" AppendMode prepareAndRun
  where
    handles = [stdout, stderr]
    prepareAndRun tmpHandle = go handles
      where
        go [] = action
        go hs = goBracket go tmpHandle hs

    goBracket _ _ [] = undefined
    goBracket go tmpHandle (h:hs) = do
      buffering <- hGetBuffering h
      let redirect = do
            old <- hDuplicate h
            hDuplicateTo tmpHandle h
            return old
          restore old = do
            hDuplicateTo old h
            hSetBuffering h buffering
            hClose old
      bracket redirect restore (\_ -> go hs)
