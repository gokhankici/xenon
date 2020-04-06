{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Analyze.FQOutAnalysis
 ( findFirstNonCTVars
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
import qualified Text.PrettyPrint.HughesPJ.Compat as PP
import           Text.Printf

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

findFirstNonCTVars :: FPResult -> AnnotationFile -> ModuleMap -> SummaryMap -> IO ()
findFirstNonCTVars fpResult af moduleMap summaryMap = do
  let result =
        (`IS.difference` IS.fromList srcNodes) $
        view nonCtVars $
        run $ execState st $ runReader r $
        worklist wl
  for_ (IS.toList result) $ \n ->
    print $ toVar n
  where
    topModuleName = af ^. afTopModule
    ModuleSummary{..} = summaryMap HM.! topModuleName
    ctVars   = findCTVars fpResult af moduleMap
    ctNodes  = IS.fromList $ toNode . T.pack <$> toList ctVars
    topMA    = af ^. afAnnotations . at topModuleName . to fromJust
    srcs     = toList $ mappend inputs $ topMA ^. moduleAnnotations . sources
    inputs   = moduleInputs (moduleMap HM.! topModuleName) mempty
    toNode   = (variableDependencyNodeMap HM.!)
    toVar    = (invVariableDependencyNodeMap IM.!)
    srcNodes = toNode <$> srcs
    fixedG =
      foldl'
      (\accG n ->
         foldl' (flip G.delLEdge) accG (G.inn accG n))
      variableDependencies
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


findCTVars :: FPResult -> AnnotationFile -> ModuleMap -> Vars
findCTVars fpResult af moduleMap = ctVars
  where
    topModuleName = af ^. afTopModule
    invMap = FCons.resSolution fpResult
    Module{..} = moduleMap HM.! topModuleName
    abIds = getData <$> alwaysBlocks
    toInvName = FT.KV . fromString . printf "inv%d"
    getCTVars n =
      HS.fromList
      . mapMaybe (bindFilter n)
      . toList
      . foldMap getBlockEqs
      . FT.splitPAnd
    ctVars =
      foldl'
      (\acc n -> acc <> getCTVars n (hmGet 0 (toInvName n) invMap))
      mempty
      abIds


getBlockEqs :: FT.Expr -> HS.HashSet Var
getBlockEqs (FT.PIff (FT.EVar v1) (FT.EVar v2)) = HS.fromList [symToVar v1, symToVar v2]
getBlockEqs _ = mempty


bindFilter :: Int -> Var -> Maybe Var
bindFilter n b =
  if "TL_" `isPrefixOf ` b
  then let s1 = drop (length "TL_V_") b
           s1Len = length s1
           s2 = take (s1Len - 2 - length (show n)) s1
       in Just s2
  else Nothing


symToVar :: FT.Symbol -> Var
symToVar = PP.render . FT.toFix
