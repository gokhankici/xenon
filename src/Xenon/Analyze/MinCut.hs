{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

{-# LANGUAGE TupleSections #-}


module Xenon.Analyze.MinCut (minCut) where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.MaxFlow

import Data.List
import Data.Ratio
import Xenon.Utils hiding (insEdge)
import Control.Lens hiding ((&), pre)
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM

type AugLabel = ( Int -- max cap
                , Int -- current flow
                , Int -- residual cap
                )

type AugDFGraph a = Gr a AugLabel

------------------------------------------------
minCut ::  (Gr a Int) -> Node -> Node -> [Edge]
------------------------------------------------
minCut gr s t = cutSet gr $ reachAtNonFullCap aug s
  where aug = mf gr s t

cutSet :: (Gr a Int) -> [Node] -> [Edge]
cutSet gr src = filter (isCut src) es
  where es = edges gr

isCut :: [Node] -> Edge -> Bool
isCut src (n,m) = (n `elem` src) && (not $ m `elem` src)

fullCap :: AugLabel -> Bool
fullCap (_,_,0) = True
fullCap _       = False

deleteFullCapEdges :: AugDFGraph a -> AugDFGraph a
deleteFullCapEdges gr = foldl deleteIfFullCap gr es
    where es = labEdges gr

deleteIfFullCap :: AugDFGraph a -> LEdge AugLabel -> AugDFGraph a
deleteIfFullCap gr e
  | fullCap $ edgeLabel e = delLEdge e gr
  | otherwise = gr

reachAtNonFullCap :: AugDFGraph a -> Node -> [Node]
reachAtNonFullCap gr n = reachable n $ deleteFullCapEdges gr

edgesToGraph :: [(Int, Int)] -> Gr () ()
edgesToGraph es = mkGraph ns es'
  where
    ns = nub $ es >>= \(n1, n2) -> (, ()) <$> [n1, n2]
    es' = [(n1, n2, ()) | (n1, n2) <- es]

testGraph0 :: Gr () ()
testGraph0 = edgesToGraph [(1,2), (1,3), (2,6), (3,4), (3,5), (4,7), (5,6), (6, 7)]

makeMincutGraph :: Eq b => Gr a b -> (Gr IS.IntSet Int, Int, Int, IM.IntMap Int)
makeMincutGraph g0 = (g3, src, snk, g0sccNodes)
  where
    (g0scc, g0sccNodes) = (_1 %~ removeSameEdges) (sccGraph g0)
    removeSameEdges g =
      let ns = labNodes g
          es = nub' (\(x,y,z) -> (x,y)) $ (_3 .~ ()) <$> labEdges g
      in mkGraph ns es
    (src, snk, g1) =
      let ns = nodes g0scc
          maxN = maximum ns
          r = maxN + 1
          l = maxN + 2
          roots  = filter (\n -> null (pre g0scc n)) ns
          leaves = filter (\n -> null (suc g0scc n)) ns
          newEdges = ((r,,undefined) <$> roots) <> ((,l,undefined) <$> leaves)
      in (r, l, foldl' (flip insEdge) (foldl' (flip insNode) g0scc ((,IS.empty) <$> [r,l])) newEdges)
    ts = topsort g1
    setEdgeCost :: Gr a b -> Gr a (Ratio Int) -> Int -> Gr a (Ratio Int)
    setEdgeCost g acc n =
      let ctx@(ps, _, a, _) = case fst $ match n acc of
                                Just m  -> m
                                Nothing -> (mempty, n, lab' (context g n), mempty)
          parentSum = sum $ fst <$> ps
          cs = suc g n
          childrenCost = if parentSum > 0 then parentSum / (fromIntegral $ length cs) else 1
          cs'  = (childrenCost ,) <$> cs
          ctx' = (mempty, n, a, cs')
      in ctx' & acc
    g2 = foldl' (setEdgeCost g1) (mkGraph (labNodes g1) mempty) ts
    costDenomLCM = foldl1' lcm $ (^. _3 . to denominator) <$> labEdges g2
    g3 = emap (\r -> toInt $ r * (fromIntegral costDenomLCM)) g2

    toInt r = numerator r `div` denominator r

-- >>> let g = makeMincutGraph testGraph0 ^. _1 in labEdges g
-- [(1,2,2),(1,3,2),(2,6,2),(3,4,1),(3,5,1),(4,7,1),(5,6,1),(6,7,3),(7,9,4),(8,1,4)]

test :: [Edge]
test = minCut g' src snk
  where
    g = testGraph0
    (g', src, snk, nodeMap) = makeMincutGraph g

-- >>> test
-- [(8,1)]
