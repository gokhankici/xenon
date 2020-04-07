{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}

module Iodine.Analyze.FQOutAnalysis
 ( findFirstNonCTVars
 , FQOutAnalysisOutput(..)
 )
where

import           Iodine.Analyze.DependencyGraph
import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Fixpoint.Common
import           Iodine.Utils

import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import           Data.List
import           Data.Maybe
import           Data.String
import qualified Data.Text as T
import qualified Language.Fixpoint.Types as FT
import qualified Language.Fixpoint.Types.Constraints as FCons
import           Polysemy
import           Polysemy.Reader
import           Polysemy.State
import           System.IO
import qualified Text.PrettyPrint.HughesPJ.Compat as PP
import           Text.Printf
-- import qualified Debug.Trace as DT

type FPResult = FCons.Result (Integer, HornClauseId)
type Var      = String
type Vars     = HS.HashSet String
type Node     = Int
type Nodes    = IS.IntSet

data WorklistR = WorklistR
  { _ctVarNodes :: Nodes
  , _sccG       :: G.Gr Nodes VarDepEdgeType
  }

data WorklistSt = WorklistSt
  { _nonCtSCCNodes :: Nodes -- scc nodes that has a non-ct var or whose parent(s) has one
  , _nonCtVars     :: Nodes
  }

makeLenses ''WorklistR
makeLenses ''WorklistSt

data FQOutAnalysisOutput = FQOutAnalysisOutput
  { firstNonCtVars :: Vars
  , ctVars         :: Vars
  , aeVars         :: Vars
  }
  deriving (Eq, Show, Read)

findFirstNonCTVars :: FPResult -> AnnotationFile -> ModuleMap -> SummaryMap -> IO FQOutAnalysisOutput
findFirstNonCTVars fpResult af moduleMap summaryMap = do
  let firstNonCtVarNodes =
        (`IS.difference` IS.fromList srcNodes) $
        view nonCtVars $
        run $ execState st $ runReader r $
        worklist wl
      firstNonCtVars =
        IS.foldl' (\acc n -> HS.insert (toVar n) acc) mempty firstNonCtVarNodes
  let docConfig =
        DocConfig $
        HM.fromList $ toList $
        ((,Blue)  . T.pack <$> toList ctVars) <>
        ((,Blue)           <$> srcs) <>
        ((,Green) . T.pack <$> toList aeVars) <>
        ((,Green)          <$> toList (topMA ^. moduleAnnotations . alwaysEquals))
  withFile "debug-ir" WriteMode $ \f -> do
    hPutStrLn f $ prettyShowWithConfig docConfig Module{..}
    hPutStrLn f ""
  return $ FQOutAnalysisOutput {..}
  where
    topModuleName = af ^. afTopModule
    ModuleSummary{..} = summaryMap HM.! topModuleName
    Module{..} = moduleMap HM.! topModuleName
    (ctVars, aeVars) = findCTVars fpResult af moduleMap
    ctNodes  = IS.fromList $ toNode . T.pack <$> toList ctVars
    topMA    = af ^. afAnnotations . at topModuleName . to fromJust
    srcs     = toList $ mappend inputs $ topMA ^. moduleAnnotations . sources
    inputs   = moduleInputs (moduleMap HM.! topModuleName) mempty
    toNode   = (variableDependencyNodeMap HM.!)
    toVar    = T.unpack . (invVariableDependencyNodeMap IM.!)
    srcNodes = toNode <$> srcs
    fixedG0 =
      foldl'
      (\g mi -> addPortDependencies mi g variableDependencyNodeMap
                & runReader summaryMap & run)
      variableDependencies
      moduleInstances
    fixedG =
      foldl'
      (\accG n ->
         foldl' (flip G.delLEdge) accG (G.inn accG n))
      fixedG0
      srcNodes
    (sg, _toSCCNodeMap) = sccGraph fixedG
    wl = G.topsort sg
    st = WorklistSt mempty mempty
    r  = WorklistR ctNodes sg

worklist :: Members '[ Reader WorklistR
                     , State  WorklistSt
                     ] r
         => [Node] -- ^ worklist
         -> Sem r ()
worklist [] = return ()
worklist (sccNode:rest) = do
  g <- asks (^.sccG)
  nonCts <- gets (^.nonCtSCCNodes)
  let parents = G.pre g sccNode
      hasBadParent = any (`IS.member` nonCts) parents
  if hasBadParent
    then modify $ nonCtSCCNodes %~ IS.insert sccNode
    else do cts <- asks (^.ctVarNodes)
            let origNodes  = G.lab' $ G.context g sccNode
                nonCtNodes = IS.filter (not . (`IS.member` cts)) origNodes
            unless (IS.null nonCtNodes) $
              modify $
              (nonCtSCCNodes %~ IS.insert sccNode) .
              (nonCtVars <>~ nonCtNodes)
  worklist rest


findCTVars :: FPResult -> AnnotationFile -> ModuleMap -> (Vars, Vars)
findCTVars fpResult af moduleMap = (ctVars, aeVars)
  where
    topModuleName = af ^. afTopModule
    invMap = FCons.resSolution fpResult
    Module{..} = moduleMap HM.! topModuleName
    abIds = getData <$> alwaysBlocks
    toInvName = FT.KV . fromString . printf "inv%d"
    go bf f n =
      HS.fromList
      . mapMaybe (bf n)
      . toList
      . foldMap f
      . FT.splitPAnd
      -- . (\a -> DT.trace (show a) a)
    getCTVars = go (bindFilter "TL_") getTagEqs
    getAEVars = go (bindFilter "VL_") getValEqs
    go2 f =
      foldl'
      (\acc n -> acc <> f n (hmGet 0 (toInvName n) invMap))
      mempty
      abIds
    ctVars = go2 getCTVars
    aeVars = go2 getAEVars


getTagEqs :: FT.Expr -> HS.HashSet Var
getTagEqs (FT.PIff (FT.EVar v1) (FT.EVar v2)) = HS.fromList [symToVar v1, symToVar v2]
getTagEqs _ = mempty

getValEqs :: FT.Expr -> HS.HashSet Var
getValEqs (FT.EEq (FT.EVar v1) (FT.EVar v2)) = HS.fromList [symToVar v1, symToVar v2]
getValEqs _ = mempty

bindFilter :: String -> Int -> Var -> Maybe Var
bindFilter prefix n b = do
  s <- stripPrefix prefix b
  let suffix = "_T" <> show n
  if suffix `isSuffixOf` s
    then Just $ take (length s - length suffix) s
    else Nothing

symToVar :: FT.Symbol -> Var
symToVar = PP.render . FT.toFix
