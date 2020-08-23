{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData #-}

module Xenon.Transform.InitVars
  ( initVars
  ) where

import           Xenon.Analyze.ModuleSummary
import           Xenon.Language.Annotation
import           Xenon.Language.IR
import           Xenon.Types

import           Control.Lens
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntMap.Strict as IM
import           Data.Maybe

initVars :: SummaryMap -> L (Module a) -> AnnotationFile -> AnnotationFile
initVars sm modules af = foldl' (\acc m -> handleModule (sm HM.! moduleName m) m acc) af modules

handleModule :: ModuleSummary -> Module a -> AnnotationFile -> AnnotationFile
handleModule ModuleSummary{..} Module{..} af =
  af & afAnnotations %~ (at moduleName ?~ newMA)
  where
    oldMA = fromMaybe emptyModuleAnnotations $ af ^. afAnnotations . at moduleName
    newMA = oldMA & moduleAnnotations %~ (alwaysEquals <>~ aeVars)
    g = variableDependencies
    rootNodes = filter (null . G.pre g) (G.nodes g)
    rootVars  = (invVariableDependencyNodeMap IM.!) <$> rootNodes
    -- aeVars = trace (show ("initVars", moduleName, _aeVars)) _aeVars
    aeVars =
      HS.fromList
      $ filter (`elem` rootVars)
      $ fst <$> toList constantInits
