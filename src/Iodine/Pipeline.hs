{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
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
import           Iodine.Transform.VariableRename
import           Iodine.Types
import           Iodine.Utils

import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict as IM
import qualified Data.Text as T
import           Polysemy
import           Polysemy.Error
import           Polysemy.Output
import           Polysemy.Reader
import           Polysemy.Trace

normalizeIR
  :: Members '[Error IodineException, Trace, Output String] r
  => AnnotationFile                          -- ^ annotation file
  -> Sem r (L (Module ()))                   -- ^ ir parser
  -> IA.IodineArgs                           -- ^ iodine args
  -> Sem r (AnnotationFile, NormalizeOutput) -- ^ annotation file & normalized IR
normalizeIR af irReader ia = do
  (af', allIR) <- variableRename af . assignThreadIds <$> irReader
  let topModuleName = af' ^. afTopModule
      ir            = topsortModules topModuleName allIR
      irMap         = mkModuleMap ir
  normalizedOutput <- runReader af' $ do
    unless (IA.noSanity ia) $
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
  => AnnotationFile                      -- ^ annotation file
  -> Sem r (L (Module ()))               -- ^ ir parser
  -> IA.IodineArgs                       -- ^ iodine args
  -> Sem r (FInfo, IM.IntMap ThreadType) -- ^ fixpoint query to run
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
    goAB ab = (getData ab, AlwaysBlockThread mn (show $ void $ abEvent ab))
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
