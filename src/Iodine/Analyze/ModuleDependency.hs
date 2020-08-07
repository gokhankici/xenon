{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

module Iodine.Analyze.ModuleDependency
 (
   topsortModules
 )
where

import           Iodine.Language.IR
import           Iodine.Types

import           Control.Carrier.State.Strict
import           Control.Carrier.Trace.Ignoring
import           Control.Lens
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import           Data.Graph.Inductive.PatriciaTree (Gr)
import qualified Data.Graph.Inductive.Query as GQ
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap as IM
import           Data.Maybe

-- import qualified Debug.Trace as DT
-- import qualified Data.Text as T
-- import Data.Graph.Inductive.Dot
-- import Text.Printf

type DepGraph = Gr () Int

data St =
  St { _depGraph      :: DepGraph
     , _moduleMap     :: HM.HashMap Id Int
     , _moduleCounter :: Int
     }
  deriving (Show)

makeLenses ''St


{- |
Sort the given modules such that if a module m1 depends on m2, m2 appears
earlier than m1 in the result.
-}
topsortModules :: Foldable t => Id -> t (Module a) -> L (Module a)
topsortModules topModuleName modules =
  foldl' (\ms n -> ms |> moduleNameMap HM.! (moduleNodes IM.! n)) mempty ts
  where
    ts = GQ.topsort filteredG
    topModuleNode =
      fromJust $
      IM.foldlWithKey'
      (\acc n mn -> if mn == topModuleName then Just n else acc)
      Nothing
      moduleNodes
    filteredG = G.nfilter reachesTopModule g
    reachesTopModule n =
      topModuleNode `elem` G.reachable n g
    moduleNameMap =
      foldl' (\acc m@Module{..} -> HM.insert moduleName m acc) mempty modules
    (g, moduleNodes) = usedByGraph modules
    -- (_g, moduleNodes) = usedByGraph modules
    -- g = DT.trace msg _g
    -- msg = unlines [ printGraph _g (T.unpack . (moduleNodes IM.!))
    --               , "total # instances " <> show totalModuleInstanceCount
    --               ]
    -- printGraph gr f =
    --   showDot $ fglToDotString $
    --   G.emap show $
    --   G.gmap (\(ps,n,_,cs) -> (ps,n,f n,cs)) $ G.grev gr
    -- totalModuleInstanceCount =
    --   let ns = G.topsort _g
    --       im = foldl' (\m n -> IM.insert n (1 + (sum $ (\(n2, c) -> (m IM.! n2) * c) <$> G.lpre _g n)) m) IM.empty ns
    --       res = im IM.! last ns
    --   in DT.trace (unlines $ (\(i :: Int, n) -> printf "%d: %s %d" i (moduleNodes IM.! n) (im IM.! n)) <$> (zip [1..] ns)) res


{- |
Creates an used-by graph for modules: (m1 --> m2) is an edge of the graph iff
module m2 instantiates m1 (or m1 is used by m2). Function also returns a mapping
between the node ids and module names.
-}
usedByGraph :: Foldable t
            => t (Module a)
            -> (DepGraph, IM.IntMap Id)
usedByGraph modules = (g, moduleNodes)
  where
    g = st ^. depGraph
    moduleNodes =
      HM.foldlWithKey' (\m name n -> IM.insert n name m) mempty (st ^. moduleMap)
    -- g' = trace traceMsg g
    -- traceMsg = unlines $ "usedByGraph" : show g : traces
    st =
      traverse_ handleModule modules
      & execState initialState
      & runTrace
      & run
    initialState =
      St { _depGraph      = G.empty
         , _moduleMap     = mempty
         , _moduleCounter = 0
         }


type FD sig m = (Has (State St) sig m, Has Trace sig m)

handleModule :: FD sig m => Module a -> m ()
handleModule Module{..} = do
  moduleNode <- getNode moduleName
  trace $ show moduleName ++ " -> " ++ show moduleNode
  for_ moduleInstances $ \ModuleInstance{..} ->
    ((, moduleNode) <$> getNode moduleInstanceType) >>= addEdge
  st <- get @St
  trace $ show moduleName ++ " st : " ++ show st

addEdge :: FD sig m => (Int, Int) -> m ()
addEdge e = modify $ depGraph %~ updateCount e

updateCount :: Num b => (Int, Int) -> Gr a b -> Gr a b
updateCount e@(fromNode, toNode) g =
  if G.hasEdge g e
  then let n = snd $ head $ filter ((== toNode) . fst) $ G.lsuc g fromNode
       in G.insEdge (fromNode, toNode, n + 1) $ G.delEdge e g
  else G.insEdge (fromNode, toNode, 1) g

getNode :: FD sig m => Id -> m Int
getNode v = do
  res <- gets (^. moduleMap . to (HM.lookup v))
  case res of
    Nothing -> do
      n <- gets (^. moduleCounter)
      modify $
        (moduleCounter +~ 1) .
        (moduleMap %~ HM.insert v n) .
        (depGraph %~ G.insNode (n, ()))
      return n
    Just n -> return n
