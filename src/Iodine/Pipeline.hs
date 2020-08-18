{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}


module Iodine.Pipeline
  ( pipeline
  , normalizeIR
  , ThreadType(..)
  , PipelineOutput
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
import           Iodine.Transform.VCGen2
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.Reader
import           Control.Effect.Error
import qualified Control.Effect.Trace as CET
import           Control.Effect.Writer
import           Control.Effect.Lift
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict as IM
import qualified Data.Text as T

-- import Iodine.Transform.Horn
-- import qualified Data.Sequence as SQ
-- import Data.Maybe

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
     , Has CET.Trace sig m
     , Has (Lift IO) sig m
     )
  => AnnotationFile                      -- ^ annotation file
  -> m (L (Module ()))                   -- ^ ir parser
  -> IA.IodineArgs                       -- ^ iodine args
  -> m (AnnotationFile, NormalizeOutput2) -- ^ annotation file & normalized IR
normalizeIR af irReader ia = do
  let topModuleName = af ^. afTopModule
  initialIR <- topsortModules topModuleName <$> irReader
  let (af', ir) = inlineInstances (af, assignThreadIds initialIR)
      irMap = mkModuleMap ir

  normalizedOutput <- runReader af' $ runReader irMap $ do
    unless (IA.benchmarkMode ia) $
      sanityCheck
      & runReader ir
    merge ir >>= normalize2

  return (af', normalizedOutput)

type PipelineOutput = ( FInfo                         -- query for fixpoint
                      , ( IM.IntMap ThreadType        -- kvar no -> thread type
                        , AnnotationFile              -- annotation file
                        , HM.HashMap Id (Module Int)  -- updated annotation file
                        , SummaryMap                  -- module summaries
                        )
                      )
{- |
Implements the following pipeline:

IR ----+                                    ModuleSummary
       |                                          |
       |                                          v
Annot ---> SanityCheck -> Merge -> Normalize -> VCGen -> Query
-}
pipeline
  :: ( Has (Error IodineException) sig m
     , Has CET.Trace sig m
     , Has (Writer Output) sig m
     , Has (Lift IO) sig m
     )
  => AnnotationFile                  -- ^ annotation file
  -> m (L (Module ()))               -- ^ ir parser
  -> IA.IodineArgs                   -- ^ iodine args
  -> m PipelineOutput -- ^ fixpoint query to run
pipeline af irReader ia = do
  (af1, normalizedOutput@(normalizedIR, _)) <- normalizeIR af irReader ia
  let normalizedIRMap = mkModuleMap normalizedIR
  moduleSummaries <-
    createModuleSummaries normalizedIR normalizedIRMap
    & runReader af1
  let af2 = initVars moduleSummaries normalizedIR af1
      af3 = let tpm = af ^. afTopModule
                m = normalizedIRMap HM.! tpm
                updateQuals m_name m_af =
                  let qs = guessQualifiers m (m_af ^. moduleAnnotations . sources) (moduleSummaries HM.! m_name)
                  in m_af & moduleQualifiers %~ mappend qs
            in af2 & afAnnotations %~ HM.adjust (updateQuals tpm) tpm
      addGuessedQuals = True
      -- addGuessedQuals = False
      finalAF = if addGuessedQuals then af3 else af2
  runReader finalAF $ do
    finfo <-
      (do vcgenOut <- vcgen normalizedOutput
          -- trace "expr count" (canonicalCount . fromJust . onlyLeft . hornBody <$> snd vcgenOut)
          constructQuery normalizedIR vcgenOut
      )
      & runReader moduleSummaries
      & runReader normalizedIRMap
    let threadTypes = foldMap toThreadType normalizedIR
    return (finfo, (threadTypes, finalAF, normalizedIRMap, moduleSummaries))

mkModuleMap :: L (Module a) -> HM.HashMap Id (Module a)
mkModuleMap = mkMap moduleName

toThreadType :: Module Int -> IM.IntMap ThreadType
toThreadType m = IM.fromList $ (getData m, ModuleSummaryThread mn) <| abts
  where
    goAB ab = (getData ab, AlwaysBlockThread mn (prettyShow $ void $ abEvent ab))
    abts = goAB <$> toList (alwaysBlocks m)
    mn = T.unpack $ moduleName m

data ThreadType =
    ModuleSummaryThread  String
  | AlwaysBlockThread    String String -- module name, event

instance Show ThreadType where
  show (ModuleSummaryThread m) = "module summary of " <> m
  show (AlwaysBlockThread m e) = m <> " -> always " <> e


-- onlyLeft :: HornExpr -> Maybe HornExpr
-- onlyLeft = \case
--   hv@HVar{} -> if hVarRun hv == LeftRun then Just hv else Nothing
--   HAnd es   -> case catMaybes' $ onlyLeft <$> es of
--                  SQ.Empty -> Nothing
--                  es' -> Just $ HAnd es'
--   HOr es    -> case catMaybes' $ onlyLeft <$> es of
--                  SQ.Empty -> Nothing
--                  es' -> Just $ HOr es'
--   e@HBinary{} ->
--     case (onlyLeft (hBinaryLhs e),  onlyLeft (hBinaryRhs e)) of
--       (Just _, Just _) -> Just e
--       _ -> Nothing
--   e@HApp{} ->
--     if any isNothing (onlyLeft <$> hAppArgs e)
--       then Nothing
--       else Just e
--   e@HInt{} -> Just e
--   e@HBool{} -> Just e
--   e@HConstant{} -> Just e
--   e@KVar{} -> Just e
--   e@HIte{} ->
--     case onlyLeft <$> [hIteCond e, hIteThen e, hIteElse e] of
--       [Just _, Just _, Just _] -> Just e
--       _ -> Nothing
--   e -> error $ unlines [ show e ]

-- -- catMaybes' :: L (Maybe a) -> L a
-- -- catMaybes' mas = mas >>= maybe SQ.empty SQ.singleton


-- canonicalCount :: HornExpr -> Integer
-- canonicalCount (HAnd es)    = product $ canonicalCount <$> es
-- canonicalCount (HOr es)     = max 1 (sum $ canonicalCount <$> es)
-- canonicalCount (HIte _ t e) = max 1 (sum $ canonicalCount <$> [t, e])
-- canonicalCount _            = 1
