{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Transform.Fixpoint.Query
  ( constructQuery
  , FInfo
  )
where

import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Fixpoint.Common
import           Iodine.Transform.Fixpoint.Qualifiers
import           Iodine.Transform.Fixpoint.SummaryQualifiers
import           Iodine.Transform.Horn
import           Iodine.Transform.VCGen
import           Iodine.Types

import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.Sequence as SQ
import qualified Language.Fixpoint.Types as FT
import           Polysemy
import           Polysemy.Reader
import           Polysemy.State

-- -----------------------------------------------------------------------------
-- generate a query for the liquid-fixpoint solver
-- -----------------------------------------------------------------------------

-- | Given the verification conditions, generate the query to be sent to the
-- fixpoint solver
constructQuery :: G r => L (Module Int) -> VCGenOutput -> Sem r FInfo
constructQuery modules (hvs, horns) = runReader hvs $ evalState initialState $ do
  setConstants
  traverse_ generateConstraint horns
  ask >>= generateAutoQualifiers
  for_ modules $ \m@Module{..} -> do
    generateWFConstraints m
    (getQualifiers moduleName >>= traverse_ generateQualifiers) & runReader m
    topModuleName <- asks (view afTopModule)
    unless (moduleName == topModuleName) $ do
      simpleCheck <- isModuleSimple m
      if simpleCheck
        then addSimpleModuleQualifiers m
        else addSummaryQualifiers m
  toFInfo
  where
    initialState = St mempty mempty mempty mempty defaultQualifiers 0 0 mempty



-- -----------------------------------------------------------------------------
-- generate constraints
-- -----------------------------------------------------------------------------

-- | Create the fixpoint version of the horn clause
generateConstraint :: FD r => Horn () -> Sem r ()
generateConstraint Horn {..} = do
  (env, (bodyExpr, headExpr)) <-
    (,) <$> convertExpr hornBody <*> convertExpr hornHead
    & runState FT.emptyIBindEnv
  n <- freshConstraintId
  let body = mkInt bodyExpr
      hd   = mkInt headExpr
      md   = HornClauseId hornStmtId hornType
      hc   = FT.mkSubC env body hd (Just n) [] md
  modify ((hornConstraints . at n) ?~ hc)


-- | Create a well formedness constraint for every statement of the module
generateWFConstraints :: FD r => Module Int -> Sem r ()
generateWFConstraints m@Module{..} = do
  generateWFConstraint moduleName m
  traverse_ (generateWFConstraint moduleName) alwaysBlocks


-- | Create a well formedness constraint for the given statement
generateWFConstraint :: (FD r, MakeKVar t)
                     => Id      -- ^ module name
                     -> t Int
                     -> Sem r ()
generateWFConstraint threadModuleName thread = do
  varNames <- askHornVariables thread
  let hornVars = setThreadId thread
                 <$> foldMap (`allHornVars` threadModuleName) varNames
  (ienv,_) <- traverse_ convertExpr hornVars & runState mempty
  case FT.wfC ienv (mkInt e) md of
    [wf] -> modify ((wellFormednessConstraints . at kvar) ?~ wf)
    wfcs -> throw $ "did not get only 1 wfc: " ++ show wfcs
 where
  tid    = getThreadId thread
  kvar   = mkKVar tid
  e      = FT.PKVar kvar mempty
  md     = HornClauseId tid WellFormed


-- -----------------------------------------------------------------------------
-- HornExpr -> FT.Expr
-- -----------------------------------------------------------------------------

-- | return the fixpoint name of the variable after updating the current bind
-- environment
convertHVar :: FDC r => Bool -> HornExpr -> Sem r FT.Expr
convertHVar isParam var@HVar{..} = do
  n <- getVariableId isParam var
  modify (FT.insertsIBindEnv [n])
  return $ FT.eVar (getFixpointName isParam var)
convertHVar _ _ =
  throw "convertHVar must be called with a Horn variable"

convertExpr :: FDC r => HornExpr -> Sem r FT.Expr

-- | create a global constant in the environment
convertExpr (HConstant c) = do
  globals <- gets (^. globalConstantLiterals)
  unless (FT.memberSEnv sym globals)
    $ modify (globalConstantLiterals %~ FT.insertSEnv sym FT.intSort)
  return $ FT.ECon $ FT.L constName FT.intSort
 where
  constName = "const_" <> c
  sym       = symbol constName

-- | return the corresponding binding for True or False
convertExpr (HBool b) = do
  be <- gets (^. invBindMap)
  let n = be HM.! name
  modify (FT.insertsIBindEnv [n])
  return $ FT.eVar name
  where name = if b then "tru" else "fals"

convertExpr (HInt i) = return . FT.ECon . FT.I . toInteger $ i

convertExpr var@HVar{} = convertHVar False var

convertExpr (HAnd es) =
  case es of
    SQ.Empty -> convertExpr (HBool True)
    _        -> FT.PAnd . toList <$> traverse convertExpr es

convertExpr (HOr es) =
  case es of
    SQ.Empty -> convertExpr (HBool False)
    _        -> FT.POr . toList <$> traverse convertExpr es

convertExpr HBinary {..} =
  toFP <$> convertExpr hBinaryLhs <*> convertExpr hBinaryRhs
  where
    toFP =
        case hBinaryOp of
          HEquals    -> FT.EEq
          HNotEquals -> FT.PAtom FT.Ne
          HImplies   -> FT.PImp
          HIff       -> FT.PIff

convertExpr HNot {..} = FT.PNot <$> convertExpr hNotArg

-- | create a new uninterpreted function if the function application does not
-- have a name for the function
convertExpr HApp {..} = do
  let fsym = symbol hAppFun
  modify (globalConstantLiterals %~ FT.insertSEnv fsym sort)
  FT.mkEApp (FT.dummyLoc fsym) . toList <$> traverse convertExpr hAppArgs
 where
  arity = SQ.length hAppArgs
  ret   = toFSort hAppRet
  sort  = if arity > 0
          then FT.mkFFunc 0 $ replicate arity FT.intSort ++ [ret]
          else ret

convertExpr KVar {..} =
  FT.PKVar (mkKVar hKVarId) . FT.mkSubst . toList <$>
  traverse
  (\(lhs, rhs) -> do
      lhs' <- convertHVar True lhs
      sym  <-
        case lhs' of
          FT.EVar v -> return v
          _ -> throw $ "expecting lhs of kvar substitution to be a symbol: " ++ show lhs
      rhs' <- convertExpr rhs
      return (sym, rhs')
  )
  hKVarSubs
