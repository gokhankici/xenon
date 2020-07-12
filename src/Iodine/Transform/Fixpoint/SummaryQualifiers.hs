{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Transform.Fixpoint.SummaryQualifiers
  ( addSimpleModuleQualifiers
  , addSummaryQualifiers
  ) where

import           Iodine.Analyze.DependencyGraph
import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Fixpoint.Common
import           Iodine.Transform.Horn
import           Iodine.Types
import           Iodine.Utils (trace, hmGet)

import           Control.Carrier.State.Strict
import           Control.Effect.Reader
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Hashable
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import           Data.Maybe
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import qualified Language.Fixpoint.Types as FT

-- -----------------------------------------------------------------------------
-- Summaries for combinatorial modules
-- -----------------------------------------------------------------------------

-- | if all inputs are ct and some of them are public, define the output color
addSimpleModuleQualifiers :: FD sig m => Module Int -> m ()
addSimpleModuleQualifiers m =
  (zip [0..] <$> asks (HM.toList . portDependencies . (HM.! moduleName m))) >>=
    traverse_
    (\(n1, (o, qd)) -> do
        let aeVars   = qd ^. implicitVars
            allVars  = (qd ^. explicitVars) <> aeVars
            aeVarsL  = toList aeVars
            allVarsL = toList allVars
            name n2  = "SimpleModule_" <> T.unpack (moduleName m) <> "_"
                       <> show n1 <> "_" <> show n2
            qs = [ mkSimpleModuleQualifierHelper m (name 0) allVarsL []       o Tag
                 , mkSimpleModuleQualifierHelper m (name 1) allVarsL aeVarsL  o Tag
                 , mkSimpleModuleQualifierHelper m (name 2) allVarsL allVarsL o Tag
                 , mkSimpleModuleQualifierHelper m (name 0) allVarsL allVarsL o Value
                 ]
        traverse_ addQualifier qs
    )


mkSimpleModuleQualifierHelper :: Module Int -> String -> [Id] -> [Id] -> Id -> HornVarType -> FT.Qualifier
mkSimpleModuleQualifierHelper m qualifierName inputs valEqInputs rhsName rhsType =
  FT.mkQual
  (FT.symbol qualifierName)
  ([ FT.QP vSymbol FT.PatNone FT.FInt
   , FT.QP (symbol "rl") (FT.PatExact $ mkRhsSymbol LeftRun)  rt
   , FT.QP (symbol "rr") (FT.PatExact $ mkRhsSymbol RightRun) rt
   ] ++
   concat [ [ FT.QP (FT.symbol $ "it" ++ show n2)     (FT.PatExact $ mkLhsSymbol i Tag LeftRun)  bt
            , FT.QP (FT.symbol $ "it" ++ show (n2+1)) (FT.PatExact $ mkLhsSymbol i Tag RightRun) bt
            ]
          | (i, n2) <- zip inputs [0,2..]
          ] ++
   concat [ [ FT.QP (FT.symbol $ "iv" ++ show n2)     (FT.PatExact $ mkLhsSymbol i Value LeftRun)  it
            , FT.QP (FT.symbol $ "iv" ++ show (n2+1)) (FT.PatExact $ mkLhsSymbol i Value RightRun) it
            ]
          | (i, n2) <- zip valEqInputs [0,2..]
          ]
  )
  (FT.PAnd lhsExprs `FT.PImp` rhsExpr)
  (FT.dummyPos "")
  where
    rhsExpr =
      case rhsType of
        Tag   -> FT.PAnd $ rhsEq:rhsTagDefs
        Value -> rhsEq
    (fpop, rt) = hornTypeToFP rhsType
    inputLen = length inputs
    rhsEq = FT.eVar @String "rl" `fpop`  FT.eVar @String "rr"
    rhsTagDefs =
      [ let isLeft = t == LeftRun
        in FT.eVar @String (if isLeft then "rl" else "rl")
           `fpop`
           FT.POr [ FT.eVar ("it" ++ show (if isLeft then n2 else n2 + 1))
                  | n2 <- take inputLen [0,2..]
                  ]
      | t <- [LeftRun, RightRun]
      ]
    lhsExprs =
      [ FT.eVar ("it" ++ show n2) `FT.PIff` FT.eVar ("it" ++ show (n2+1))
      | (_, n2) <- zip inputs [0,2..]
      ] ++
      [ FT.eVar ("iv" ++ show n2) `FT.EEq` FT.eVar ("iv" ++ show (n2+1))
      | (_, n2) <- zip valEqInputs [0,2..]
      ]
    mkRhsSymbol r = symbol $ getFixpointName True $ mkVar rhsName rhsType r
    mkLhsSymbol v t r = symbol $ getFixpointName True $ mkVar v t r
    mkVar v t r = setThreadId m $ HVar0 v (moduleName m) t r
    bt = FT.boolSort
    it = FT.intSort
{- HLINT ignore mkSimpleModuleQualifierHelper -}


-- -----------------------------------------------------------------------------
-- Summaries for sub modules
-- -----------------------------------------------------------------------------

addSummaryQualifiers :: FD sig m => Module Int -> m ()
addSummaryQualifiers m@Module{..} = do
  addSimpleModuleQualifiers m
  traverse_ (addSummaryQualifiersAB moduleName) alwaysBlocks


addSummaryQualifiersAB :: FD sig m => Id -> AlwaysBlock Int -> m ()
addSummaryQualifiersAB moduleName ab = do
  sqvs <- summaryQualifierVariablesAB moduleName ab
  for_ (HM.toList sqvs) $ \(v, lqds) -> flip SQ.traverseWithIndex lqds $ \n qds -> do
    trace "addSummaryQualifiersAB" (getThreadId ab, v, qds)
    let evs    = qds ^. explicitVars
        ivs    = qds ^. implicitVars
        allEqs = HS.toList (evs <> ivs)
        valEqs = HS.toList ivs
        nstr   = "_" <> show n
        qs = [ mkSummaryQualifierHelper ab moduleName
               (namePrefix <> T.unpack v <> "_Tag1" <> nstr)
               allEqs mempty v Tag
             , mkSummaryQualifierHelper ab moduleName
               (namePrefix <> T.unpack v <> "_Tag2" <> nstr)
               allEqs valEqs v Tag
             , mkSummaryQualifierHelper ab moduleName
               (namePrefix <> T.unpack v <> "_Tag3" <> nstr)
               allEqs allEqs v Tag
             , mkSummaryQualifierHelper ab moduleName
               (namePrefix <> T.unpack v <> "_Value" <> nstr)
               mempty allEqs v Value
             ]
    for_ qs addQualifier
  where
    namePrefix =
      "SummaryQualifierAB_"
      <> T.unpack moduleName <> "_"
      <> "T" <> show (getThreadId ab) <> "_"


type QDM  = HM.HashMap Id QualifierDependencies
type QDMs = HM.HashMap Id (L QualifierDependencies)

summaryQualifierVariablesAB :: ( Has (Reader SummaryMap) sig m
                               , Has (Reader (HM.HashMap Id M)) sig m
                               , Has (Reader AnnotationFile) sig m
                               -- , Effect sig
                               )
                            => Id -- ^ module name
                            -> AlwaysBlock Int
                            -> m QDMs
summaryQualifierVariablesAB moduleName ab = do
  ModuleSummary{..} <- asks (hmGet 2 moduleName)
  abVars <- getUpdatedVariables (AB ab)
  let toNode v = variableDependencyNodeMap HM.! v
      abNodes = toNode <$> HS.toList abVars
  let toVar n = invVariableDependencyNodeMap IM.! n
      addParent l uName =
        case l of
          Implicit -> implicitVars %~ HS.insert uName
          Explicit -> explicitVars %~ HS.insert uName
  if isStar ab
    then do
    m1 <-
      execState (mempty :: QDM) $
      for_ abNodes $ \v -> do
      let vName = toVar v
      for_ (G.lpre variableDependencies v) $ \(u, l) -> do
        let uName = toVar u
        unless (v == u) $ do
          oldQD <- fromMaybe mempty <$> gets @QDM (^.at vName)
          modify @QDM (at vName ?~ addParent l uName oldQD)

    m2 <-
      execState (mempty :: QDM) $
      for_ (G.topsort variableDependencies) $ \v -> do
      let vName = toVar v
      for_ (G.lpre variableDependencies v) $ \(u, l) -> do
        let uName = toVar u
        unless (v == u) $ do
          muQD <- gets @QDM (^.at uName)
          oldQD <- fromMaybe mempty <$> gets @QDM (^.at vName)
          case muQD of
            Nothing -> -- u is a root node
              modify @QDM (at vName ?~ addParent l uName oldQD)
            Just uQD ->
              case l of
                Implicit -> do
                  let uQDVars = (uQD ^. implicitVars) <> (uQD ^. explicitVars)
                      newQD   = oldQD & (implicitVars <>~ uQDVars)
                  modify @QDM (at vName ?~ newQD)
                Explicit ->
                  modify @QDM (at vName ?~ uQD <> oldQD)

    return $ mergeQDMaps m1 m2
    else do
    let (g, toSCCNodeMap) = (variableDependenciesSCC, variableDependencySCCNodeMap)
        toVars n = case fst $ G.match n g of
                     Just (_, _, is, _) -> IS.toList is
                     Nothing -> error "unreachable"
    m1 <-
      execState (mempty :: QDM) $ do
      for_ (G.topsort g) $ \sccV ->
        for_ (toVars sccV) $ \v -> do
          let vName = toVar v
          for_ (G.lpre g sccV) $ \(sccU, l) ->
            for_ (toVars sccU) $ \u -> do
            -- if variableDependencies `G.hasLEdge` (u, v, l)
            let uName = toVar u
            mUQD <- gets @QDM (^.at uName)
            oldQD <- fromMaybe mempty <$> gets @QDM (^.at vName)
            case (mUQD, l) of
              (Nothing, _) ->
                modify @QDM (at vName ?~ addParent l uName oldQD)
              (Just uQD, Implicit) -> do
                let uQDVars = (uQD ^. implicitVars) <> (uQD ^. explicitVars)
                    newQD = oldQD & implicitVars %~ mappend uQDVars
                modify @QDM (at vName ?~ newQD)
              (Just uQD, Explicit) ->
                modify @QDM (at vName ?~ oldQD <> uQD)
      modify @QDM (HM.filterWithKey (\k _ -> k `elem` abVars))

    m2 <-
      execState (mempty :: QDM) $
      for_ abNodes $ \v -> do
        let vName = toVar v
            sccV  = toSCCNodeMap IM.! v
        for_ (G.lpre g sccV) $ \(sccU, l) ->
          for_ (toVars sccU) $ \u -> do
          let uName = toVar u
          oldQD <- fromMaybe mempty <$> gets @QDM (^.at vName)
          modify @QDM (at vName ?~ addParent l uName oldQD)

    return $ mergeQDMaps m1 m2

mergeQDMaps :: (Eq k, Hashable k, Eq a)
            => HM.HashMap k a
            -> HM.HashMap k a
            -> HM.HashMap k (L a)
mergeQDMaps m1 m2 =
  HM.unionWith mrg (HM.map SQ.singleton m1) (HM.map SQ.singleton m2)
  where
    mrg l1 l2 = l1 <> SQ.filter (`notElem` l1) l2

-- | given a list of input ports i1, i2, ... creates a qualifier of the form:
-- ((TL_i1 <=> TR_i1) && (TL_i2 <=> TR_i2) && ...) ==> TL_$1 <=> TR_$1)
mkSummaryQualifierHelper :: MakeKVar k
                         => k Int       -- ^ always block or module
                         -> Id          -- ^ module name
                         -> String      -- ^ qualifier name
                         -> [Id]        -- ^ inputs
                         -> [Id]        -- ^ always_equal inputs
                         -> Id
                         -> HornVarType -- ^ type of the right hand side
                         -> FT.Qualifier
mkSummaryQualifierHelper kv moduleName qualifierName inputs valEqInputs output rhsType =
  FT.mkQual
  (FT.symbol qualifierName)
  ([ FT.QP vSymbol FT.PatNone FT.FInt
   , FT.QP (symbol "rl") (FT.PatExact $ mkRhsSymbol LeftRun)  rt
   , FT.QP (symbol "rr") (FT.PatExact $ mkRhsSymbol RightRun) rt
   ] ++
   concat [ [ FT.QP (FT.symbol $ "it" ++ show n2)     (FT.PatExact $ mkLhsSymbol i Tag LeftRun)  bt
            , FT.QP (FT.symbol $ "it" ++ show (n2+1)) (FT.PatExact $ mkLhsSymbol i Tag RightRun) bt
            ]
          | (i, n2) <- zip inputs [0,2..]
          ] ++
   concat [ [ FT.QP (FT.symbol $ "iv" ++ show n2)     (FT.PatExact $ mkLhsSymbol i Value LeftRun)  it
            , FT.QP (FT.symbol $ "iv" ++ show (n2+1)) (FT.PatExact $ mkLhsSymbol i Value RightRun) it
            ]
          | (i, n2) <- zip valEqInputs [0,2..]
          ]
  )
  (FT.PAnd lhsExprs `FT.PImp` (FT.eVar @String "rl" `fpop`  FT.eVar @String "rr"))
  (FT.dummyPos "")
  where
    (fpop, rt) = hornTypeToFP rhsType
    lhsExprs =
      [ FT.eVar ("it" ++ show n2) `FT.PIff` FT.eVar ("it" ++ show (n2+1))
      | (_, n2) <- zip inputs [0,2..]
      ] ++
      [ FT.eVar ("iv" ++ show n2) `FT.EEq` FT.eVar ("iv" ++ show (n2+1))
      | (_, n2) <- zip valEqInputs [0,2..]
      ]
    mkRhsSymbol r =
      symbol $
      getFixpointName True $
      mkVar output rhsType r
    mkLhsSymbol v t r =
      symbol $
      getFixpointName True $
      mkVar v t r
    mkVar v t r =
      setThreadId kv $ HVar0 v moduleName t r
    bt = FT.boolSort
    it = FT.intSort
