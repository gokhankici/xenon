{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
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
-- import           Iodine.Utils

import           Control.Lens
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import           Data.Graph.Inductive.PatriciaTree (Gr)
import qualified Data.Graph.Inductive.Query as GQ
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap as IM
import           Data.Maybe
import           Polysemy
import           Polysemy.State
import qualified Polysemy.Trace as PT

-- import qualified Debug.Trace as DT
-- import qualified Data.Text as T

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
    (g, moduleNodes) = usedByGraph modules
    filteredG = G.nfilter reachesTopModule g
    reachesTopModule n =
      topModuleNode `elem` G.reachable n g
    -- (_g, moduleNodes) = usedByGraph modules
    -- g = DT.trace (printGraph _g (T.unpack . (moduleNodes IM.!))) _g
    moduleNameMap =
      foldl' (\acc m@Module{..} -> HM.insert moduleName m acc) mempty modules


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
      & PT.ignoreTrace -- PT.runTraceList
      & run
    initialState =
      St { _depGraph      = G.empty
         , _moduleMap     = mempty
         , _moduleCounter = 0
         }


type FD r = Members '[State St, PT.Trace] r

handleModule :: FD r => Module a -> Sem r ()
handleModule Module{..} = do
  moduleNode <- getNode moduleName
  PT.trace $ show moduleName ++ " -> " ++ show moduleNode
  for_ moduleInstances $ \ModuleInstance{..} ->
    ((, moduleNode) <$> getNode moduleInstanceType) >>= addEdge
  st <- get
  PT.trace $ show moduleName ++ " st : " ++ show st

addEdge :: FD r => (Int, Int) -> Sem r ()
addEdge e = modify $ depGraph %~ updateCount e

updateCount :: Num b => (Int, Int) -> Gr a b -> Gr a b
updateCount e@(fromNode, toNode) g =
  if G.hasEdge g e
  then let n = snd $ head $ filter ((== toNode) . fst) $ G.lsuc g fromNode
       in G.insEdge (fromNode, toNode, n + 1) $ G.delEdge e g
  else G.insEdge (fromNode, toNode, 1) g

getNode :: FD r => Id -> Sem r Int
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
