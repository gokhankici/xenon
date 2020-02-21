{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Analyze.ModuleSummary
  (
    createModuleSummaries
  -- , tryToSummarize
  , ModuleSummary(..)
  , SummaryMap
  )
where

import           Iodine.Analyze.DependencyGraph
import           Iodine.Analyze.ModuleDependency
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Lens
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive.Query as GQ
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.Sequence as SQ
import           Data.Traversable
import           Polysemy
import           Polysemy.Reader
import           Polysemy.State
import           Polysemy.Trace

type ModuleMap   = HM.HashMap Id (Module ())
type SummaryMap  = HM.HashMap Id ModuleSummary

data ModuleSummary =
  ModuleSummary {  -- | the dependency map between ports: from an output to the
                   -- set of inputs that affect it
                  portDependencies :: HM.HashMap Id Ids,

                  -- | whether the module is a combinational logic (i.e., does
                  -- not have a clock)
                  isCombinatorial :: Bool
                }
  deriving (Show)

-- #############################################################################

{- |
Create a summary for each given module
-}
createModuleSummaries :: Members '[ Reader AnnotationFile
                                  , Trace
                                  ] r
                      => ModuleMap -> Sem r SummaryMap
createModuleSummaries moduleMap =
  for_ orderedModules (\m@Module{..} ->
      createModuleSummary m >>= (modify . HM.insert moduleName))
  & runState @SummaryMap mempty
  & fmap fst
  where
    orderedModules :: L (Module ())
    orderedModules = topsortModules moduleMap


createModuleSummary :: Members '[ Reader AnnotationFile
                                , State SummaryMap
                                , Trace
                                ] r
                    => Module ()
                    -> Sem r ModuleSummary
createModuleSummary m@Module{..} = do
  (varDepGraph, varDepMap) <- dependencyGraphFromModule m
  let lookupNode v = mapLookup 1 v varDepMap
  clk <- view clock <$> getModuleAnnotations moduleName
  let hasClock = clk /= Nothing
      isClk v = clk == Just v
  let portDependencies =
        foldl'
        (\deps o ->
           let is = HS.fromList $ toList $
                    SQ.filter
                    (\i -> not (isClk i) && (isReachable varDepGraph (lookupNode o) . lookupNode) i)
                    inputs
           in  HM.insert o is deps)
        mempty
        outputs

  -- we can summarize the module instance if itself does not have a clock and
  -- all of its submodules can be summarized
  submodulesCanBeSummarized <-
    fmap and $
    forM moduleInstances $ \ModuleInstance{..} ->
    isCombinatorial <$> gets (mapLookup 2 moduleInstanceType)
  let isCombinatorial = not hasClock && submodulesCanBeSummarized

  return ModuleSummary {..}
  where
    isReachable g toNode fromNode =
      let ns = GQ.reachable fromNode g
      in toNode `elem` ns

    inputs, outputs :: L Id
    (inputs, outputs) =
      foldl' (\acc -> \case
                 Input i  -> acc & _1 %~ (|> variableName i)
                 Output o -> acc & _2 %~ (|> variableName o)) mempty ports


dependencyGraphFromModule :: Members '[State SummaryMap] r
                          => Module ()
                          -> Sem r (VarDepGraph, HM.HashMap Id Int)
dependencyGraphFromModule Module{..} =
  if   SQ.null moduleInstances
  then return (g, nodeMap)
  else do
    extraEdges <- foldlM' SQ.empty moduleInstances $ \es ModuleInstance{..} -> do
      ModuleSummary{..} <- gets (mapLookup 3 moduleInstanceType)
      let assignedVars p = toList . getVariables $ mapLookup 4 p moduleInstancePorts
      return $
        HM.foldlWithKey'
        (\es2 o is ->
            foldl' (|>) es2
            [ (lookupNode fromVar, lookupNode toVar, Explicit Blocking)
            | i <- toList is
            , fromVar <- assignedVars i
            , toVar   <- assignedVars o
            ]
        )
        es
        portDependencies
    return (foldr' G.insEdge g extraEdges, nodeMap)
  where
    lookupNode v = mapLookup 5 v nodeMap
    (g, nodeMap) = dependencyGraphFromMany (gateStmts <> fmap abStmt alwaysBlocks)


-- #############################################################################

-- {- |
-- Turn the given module instances to always-* blocks if possible.
-- -}
-- tryToSummarize :: (Member (Reader SummaryMap) r, Foldable t)
--                => t (ModuleInstance ())
--                -> Sem r (L (AlwaysBlock ()), L (ModuleInstance ()))
-- tryToSummarize mis =
--   foldlM' mempty mis $ \acc mi -> do
--   mAB <- summarizeAsAlwaysStar mi
--   return $
--     case mAB of
--       Nothing -> acc & _2 %~ (|> mi)
--       Just ab -> acc & _1 %~ (|> ab)


-- summarizeAsAlwaysStar :: Member (Reader SummaryMap) r
--                       => ModuleInstance ()
--                       -> Sem r (Maybe (AlwaysBlock ()))
-- summarizeAsAlwaysStar ModuleInstance{..} = do
--   ModuleSummary{..} <- asks (HM.! moduleInstanceType)
--   return $
--     if isCombinatorial
--     then Just $ AlwaysBlock Star $ SummaryStmt moduleInstanceType moduleInstancePorts ()
--     else Nothing

mapLookup :: Show a => Int -> Id -> HM.HashMap Id a -> a
mapLookup n k m =
  case HM.lookup k m of
    Nothing ->
      error $ unlines [ "ModuleSummary.mapLookup: " ++ show n
                      , "map: " ++ show m
                      , "key:" ++ show k
                      ]
    Just a  -> a
