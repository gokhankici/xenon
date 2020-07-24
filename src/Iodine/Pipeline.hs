{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}


module Iodine.Pipeline
  ( pipeline
  , normalizeIR
  , ThreadType(..)
  ) where

import           Iodine.Analyze.GuessQualifiers
import           Iodine.Analyze.ModuleDependency (topsortModules)
import           Iodine.Analyze.ModuleSummary
import qualified Iodine.IodineArgs as IA
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Fixpoint.Query
import           Iodine.Transform.InitVars
import           Iodine.Transform.Inline
import           Iodine.Transform.Merge
import           Iodine.Transform.Normalize
import           Iodine.Transform.SanityCheck
import           Iodine.Transform.VCGen
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.Reader
import           Control.Effect.Error
import           Control.Effect.Trace
import           Control.Effect.Writer
import           Control.Effect.Lift
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict as IM
import qualified Data.Text as T

{- |
1. Give unique id to all things.
2. Run sanity check
3. Inline if requested
4. Merge the blocks
5. Normalize
-}
normalizeIR
  :: ( Has (Error IodineException) sig m
     , Has (Writer Output) sig m
     , Has (Lift IO) sig m
     )
  => AnnotationFile                      -- ^ annotation file
  -> m (L (Module ()))                   -- ^ ir parser
  -> IA.IodineArgs                       -- ^ iodine args
  -> m (AnnotationFile, NormalizeOutput) -- ^ annotation file & normalized IR
normalizeIR af irReader ia = do
  let topModuleName = af ^. afTopModule
  initialIR <- topsortModules topModuleName <$> irReader
  let (af', ir) = inlineInstances $
                  (af, assignThreadIds initialIR)
      irMap = mkModuleMap ir

  normalizedOutput <- runReader af' $ runReader irMap $ do
    unless (IA.benchmarkMode ia) $
      sanityCheck
      & runReader ir
    merge ir >>= normalize

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
     , Has (Lift IO) sig m
     )
  => AnnotationFile                  -- ^ annotation file
  -> m (L (Module ()))               -- ^ ir parser
  -> IA.IodineArgs                   -- ^ iodine args
  -> m (FInfo, (IM.IntMap ThreadType, AnnotationFile, HM.HashMap Id (Module Int), SummaryMap)) -- ^ fixpoint query to run
pipeline af irReader ia = do
  (af1, normalizedOutput@(normalizedIR, _)) <- normalizeIR af irReader ia
  let normalizedIRMap = mkModuleMap normalizedIR
  moduleSummaries <-
    createModuleSummaries normalizedIR normalizedIRMap
    & runReader af1
  let af2 = initVars moduleSummaries normalizedIR af1
      af3 = let tpm = af ^. afTopModule
                updateQuals m_name m_af =
                  let qs = guessQualifiers (m_af ^. moduleAnnotations . sources) (moduleSummaries HM.! m_name)
                  in m_af & moduleQualifiers %~ mappend qs
            in af2 & afAnnotations %~ HM.adjust (updateQuals tpm) tpm
      addGuessedQuals = True
      -- addGuessedQuals = False
      finalAF = if addGuessedQuals then af3 else af2
  runReader finalAF $ do
    finfo <-
      (vcgen normalizedOutput >>= constructQuery normalizedIR)
      & runReader moduleSummaries
      & runReader normalizedIRMap
    let threadTypes = foldMap toThreadType normalizedIR
    return (finfo, (threadTypes, finalAF, normalizedIRMap, moduleSummaries))

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
