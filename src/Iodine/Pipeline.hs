{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}


module Iodine.Pipeline
  ( pipeline
  , normalizeIR
  ) where

import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Fixpoint.Query
import           Iodine.Transform.Merge
import           Iodine.Transform.Normalize
import           Iodine.Transform.SanityCheck
import           Iodine.Transform.VCGen
import           Iodine.Transform.VariableRename
import           Iodine.Types

import           Data.Foldable
import           Data.Function
import qualified Data.HashMap.Strict as HM
import           Polysemy
import           Polysemy.Error
import           Polysemy.Output
import           Polysemy.Reader
import           Polysemy.Trace

normalizeIR
  :: Members '[Error IodineException, Trace, Output String] r
  => AnnotationFile             -- ^ annotation file
  -> Sem r (L (Module ()))      -- ^ ir parser
  -> Sem r (AnnotationFile, NormalizeOutput) -- ^ annotation file & normalized IR
normalizeIR af irReader = do
  (af', ir) <- variableRename af . assignThreadIds <$> irReader
  let irMap = mkModuleMap ir
  normalizedOutput <- runReader af' $ do
    sanityCheck
      & runReader ir
      & runReader irMap
    (merge ir & runReader irMap) >>= normalize
  return (af', normalizedOutput)


{- |
Implements the following pipeline:

IR ----+                                    ModuleSummary
       |                                          |
       |                                          v
Annot ---> SanityCheck -> Merge -> Normalize -> VCGen -> Query
-}
pipeline
  :: Members '[Error IodineException, Trace, Output String] r
  => AnnotationFile             -- ^ annotation file
  -> Sem r (L (Module ()))      -- ^ ir parser
  -> Sem r FInfo                -- ^ fixpoint query to run
pipeline af irReader = do
  (af', normalizedOutput@(normalizedIR, _)) <- normalizeIR af irReader
  runReader af' $ do
    let normalizedIRMap = mkModuleMap normalizedIR
    moduleSummaries <- createModuleSummaries normalizedIRMap
    (vcgen normalizedOutput >>= constructQuery normalizedIR)
      & runReader moduleSummaries
      & runReader normalizedIRMap


mkModuleMap :: L (Module a) -> HM.HashMap Id (Module a)
mkModuleMap =
  foldl' (\acc m@Module{..} -> HM.insert moduleName m acc) mempty
