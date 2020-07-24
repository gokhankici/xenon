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

import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Fixpoint.Common
import           Iodine.Transform.Fixpoint.Qualifiers
import           Iodine.Transform.Fixpoint.SummaryQualifiers
import           Iodine.Transform.Horn
import           Iodine.Transform.VCGen
import           Iodine.Types

import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import           Data.Maybe
import qualified Data.Sequence as SQ
import qualified Language.Fixpoint.Types as FT

-- -----------------------------------------------------------------------------
-- generate a query for the liquid-fixpoint solver
-- -----------------------------------------------------------------------------

-- | Given the verification conditions, generate the query to be sent to the
-- fixpoint solver
constructQuery :: G sig m => L (Module Int) -> VCGenOutput -> m FInfo
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
    initialState = St mempty mempty mempty mempty defaultQualifiers 0 0 mempty mempty



-- -----------------------------------------------------------------------------
-- generate constraints
-- -----------------------------------------------------------------------------

-- | Create the fixpoint version of the horn clause
generateConstraint :: FD sig m => Horn () -> m ()
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
generateWFConstraints :: FD sig m => Module Int -> m ()
generateWFConstraints m@Module{..} = do
  generateWFConstraint moduleName m
  traverse_ (generateWFConstraint moduleName) alwaysBlocks


-- | Create a well formedness constraint for the given statement
generateWFConstraint :: (FD sig m, MakeKVar t)
                     => Id      -- ^ module name
                     -> t Int
                     -> m ()
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
convertHVar :: FDC sig m => Bool -> HornExpr -> m FT.Expr
convertHVar isParam var@HVar{..} = do
  (n, fpVar) <- getVariableId isParam var
  modify (FT.insertsIBindEnv [n])
  return fpVar
convertHVar _ _ =
  throw "convertHVar must be called with a Horn variable"

convertExpr :: FDC sig m => HornExpr -> m FT.Expr

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
convertExpr e@(HBool _) = do
  (n, v) <- fromJust <$> gets (^. invConstBindMap . at e)
  modify (FT.insertsIBindEnv [n])
  return v

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

convertExpr KVar {..} = do
  let moduleName =
        case SQ.viewl hKVarSubs of
          SQ.EmptyL        -> Nothing
          (lhs, _) SQ.:< _ -> Just $ hVarModule lhs
  mms <- maybe (return Nothing) (\mn -> asks @SummaryMap (^. at mn)) moduleName
  let tmpCheck e =
        case mms of
          Just ms -> hVarName e `notElem` temporaryVariables ms
          Nothing -> error "unreachable"
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
    -- hKVarSubs
    (SQ.filter (tmpCheck . fst) hKVarSubs)

convertExpr HIte{..} =
  FT.EIte
  <$> convertExpr hIteCond
  <*> convertExpr hIteThen
  <*> convertExpr hIteElse
