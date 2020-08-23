{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}

module Xenon.Analyze.FQOutAnalysis
 ( findFirstNonCTVars
 , FQOutAnalysisOutput(..)
 )
where

import           Xenon.Analyze.DependencyGraph
import           Xenon.Analyze.ModuleSummary
import           Xenon.Language.Annotation
import           Xenon.Language.IR
import           Xenon.Transform.Fixpoint.Common
import           Xenon.Utils

import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
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
import           Data.Monoid
import qualified Data.Sequence as SQ
import           Data.String
import qualified Data.Text as T
import qualified Language.Fixpoint.Types as FT
import qualified Language.Fixpoint.Types.Constraints as FCons
import           System.IO
import qualified Text.PrettyPrint.HughesPJ.Compat as PP
import           Text.Printf
-- import qualified Debug.Trace as DT

type FPResult = FCons.Result (Integer, HornClauseId)
type Var      = String
type Vars     = HS.HashSet String
type VarsMap  = IM.IntMap Vars
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

type VarsDisagree = [(Int, Int, Vars)]

data FQOutAnalysisOutput = FQOutAnalysisOutput
  { firstNonCtVars :: Vars
  , ctVars         :: VarsMap
  , aeVars         :: VarsMap
  , ctVarsDisagree :: VarsDisagree
  , aeVarsDisagree :: VarsDisagree
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
  let maybeLookup e l = if e `elem` l then Just e else Nothing
      colorMapHelper vm c n v =
        c <$ (IM.lookup n vm >>= maybeLookup (T.unpack v))
  let docConfig =
        defaultDocConfig
        { varColorMap =
          \n v -> getFirst $
                  First (colorMapHelper aeVars Green n v) <>
                  First (colorMapHelper ctVars Blue n v)
        }
  withFile "debug-ir" WriteMode $ \f -> do
    hPutStrLn f $ prettyShowWithConfig docConfig Module{..}
    hPutStrLn f ""
  return $ FQOutAnalysisOutput {..}
  where
    topModuleName     = af ^. afTopModule
    ModuleSummary{..} = summaryMap HM.! topModuleName
    m@Module{..}      = moduleMap HM.! topModuleName
    (ctVars, aeVars)  = findCTVars fpResult af moduleMap
    (ctVarsCommon, ctVarsDisagree) = mergeVarsMap m ctVars
    aeVarsDisagree = snd $ mergeVarsMap m aeVars
    ctNodes  = IS.fromList $ toNode . T.pack <$> toList ctVarsCommon
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

mergeVarsMap :: Module Int -> VarsMap -> (Vars, VarsDisagree)
mergeVarsMap Module{..} vsm = ( foldMap fst comparisons
                              , keepDisagreedVars comparisons
                              )
  where
    keepDisagreedVars = foldMap (\(_, t) -> [t | not $ HS.null (t^._3)])

    comparisons :: SQ.Seq (Vars, (Int, Int, Vars))
    comparisons = do
      (n1, n2) <- choose2 $ getData <$> alwaysBlocks
      let getVars n = IM.findWithDefault mempty n vsm
          vs1       = getVars n1
          vs2       = getVars n2
          common    = vs1 `HS.intersection` vs2
          disagree  = vs1 `HS.difference` vs2
      return (common, (n1, n2, disagree))

    choose2 :: SQ.Seq a -> SQ.Seq (a, a)
    choose2 = \case
      SQ.Empty          -> mempty
      _ SQ.:<| SQ.Empty -> mempty
      a SQ.:<| rest     -> ((a,) <$> rest) <> ((,a) <$> rest) <> choose2 rest



worklist :: ( Has (Reader WorklistR) sig m
            , Has (State  WorklistSt) sig m
            )
         => [Node] -- ^ worklist
         -> m ()
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


findCTVars :: FPResult -> AnnotationFile -> ModuleMap -> (VarsMap, VarsMap)
findCTVars fpResult af moduleMap = (ctVars, aeVars)
  where
    topModuleName = af ^. afTopModule
    invMap = FCons.resSolution fpResult
    Module{..} = moduleMap HM.! topModuleName
    abIds = getData <$> alwaysBlocks
    toInvName = FT.KV . fromString . printf "inv%d"
    getVars :: (Int -> Var -> Maybe Var) -> (FT.Expr -> Vars) -> Int -> FT.Expr -> Vars
    getVars bf f n = HS.fromList
                     . mapMaybe (bf n)
                     . toList
                     . foldMap f
                     . FT.splitPAnd
    createVarsMap f = foldl'
                      (\acc n ->
                         case HM.lookup (toInvName n) invMap of
                           Just x -> IM.insert n (f n x) acc
                           Nothing -> acc)
                      mempty
                      abIds
    ctVars = createVarsMap $ getVars (bindFilter "TL_") getTagEqs
    aeVars = createVarsMap $ getVars (bindFilter "VL_") getValEqs


getTagEqs :: FT.Expr -> Vars
getTagEqs (FT.PIff (FT.EVar v1) (FT.EVar v2)) = HS.fromList [symToVar v1, symToVar v2]
getTagEqs _ = mempty

getValEqs :: FT.Expr -> Vars
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
