{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}


module Iodine.Pipeline
  ( pipeline
  , normalizeIR
  , ThreadType(..)
  ) where

import           Iodine.Analyze.ModuleDependency (topsortModules)
import           Iodine.Analyze.ModuleSummary
import qualified Iodine.IodineArgs as IA
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Fixpoint.Query
import           Iodine.Transform.InitVars
import           Iodine.Transform.Merge
import           Iodine.Transform.Normalize
import           Iodine.Transform.SanityCheck
import           Iodine.Transform.VCGen
-- import           Iodine.Transform.VariableRename
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.Reader
import           Control.Effect.Error
import           Control.Effect.Trace
import           Control.Effect.Writer
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict as IM
import qualified Data.Text as T

normalizeIR
  :: ( Has (Error IodineException) sig m
     , Has (Writer Output) sig m
     , Effect sig
     )
  => AnnotationFile                      -- ^ annotation file
  -> m (L (Module ()))                   -- ^ ir parser
  -> IA.IodineArgs                       -- ^ iodine args
  -> m (AnnotationFile, NormalizeOutput) -- ^ annotation file & normalized IR
normalizeIR af irReader ia = do
  -- (af', allIR) <- variableRename af . assignThreadIds <$> irReader
  let af' = af
  allIR <- assignThreadIds <$> irReader
  let topModuleName = af' ^. afTopModule
      ir            = topsortModules topModuleName allIR
      irMap         = mkModuleMap ir
  normalizedOutput <- runReader af' $ do
    unless (IA.benchmarkMode ia) $
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
  :: ( Has (Error IodineException) sig m
     , Has Trace sig m
     , Has (Writer Output) sig m
     , Effect sig
     )
  => AnnotationFile                  -- ^ annotation file
  -> m (L (Module ()))               -- ^ ir parser
  -> IA.IodineArgs                   -- ^ iodine args
  -> m (FInfo, IM.IntMap ThreadType) -- ^ fixpoint query to run
pipeline af irReader ia = do
  (af', normalizedOutput@(normalizedIR, _)) <- normalizeIR af irReader ia
  let normalizedIRMap = mkModuleMap normalizedIR
  moduleSummaries <-
    createModuleSummaries normalizedIR normalizedIRMap
    & runReader af'
  let af'' = initVars moduleSummaries normalizedIR af'
  runReader af'' $ do
    finfo <-
      (vcgen normalizedOutput >>= constructQuery normalizedIR)
      & runReader moduleSummaries
      & runReader normalizedIRMap
    let threadTypes = foldMap toThreadType normalizedIR
    return (finfo, threadTypes)

mkModuleMap :: L (Module a) -> HM.HashMap Id (Module a)
mkModuleMap = mkMap moduleName

toThreadType :: Module Int -> IM.IntMap ThreadType
toThreadType m = IM.fromList $ (getData m, ModuleSummaryThread mn) <| abts <> mits
  where
    goAB ab = (getData ab, AlwaysBlockThread mn (prettyShow $ void $ abEvent ab))
    abts = goAB <$> toList (alwaysBlocks m)
    goMI mi = (getData mi, ModuleInstanceThread mn (T.unpack $ moduleInstanceType mi))
    mits = goMI <$> toList (moduleInstances m)
    mn = T.unpack $ moduleName m

data ThreadType =
    ModuleSummaryThread  String
  | AlwaysBlockThread    String String -- module name, event
  | ModuleInstanceThread String String -- module name, instance type

instance Show ThreadType where
  show (ModuleSummaryThread m)    = "module summary of " <> m
  show (AlwaysBlockThread m e)    = m <> " -> always " <> e
  show (ModuleInstanceThread m t) = m <> " -> module instance of " <> t
