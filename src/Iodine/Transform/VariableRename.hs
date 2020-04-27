{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module Iodine.Transform.VariableRename (variableRename) where

import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types

import           Control.Lens
import           Control.Monad
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS



-- newtype St = St { getModuleInputs :: HM.HashMap Id Ids }

-- type FD sig m  = Has (Reader St) sig m
-- type FDM sig m = (FD sig m, Has (Reader Ids) sig m)

-- inputPrefix, nonInputPrefix :: Id
-- inputPrefix    = "I_"
-- nonInputPrefix = "NI_"

type FD sig m  = Monad m
type FDM sig m = Monad m

varPrefix :: Id
varPrefix = "_"

-- | renames all the variables in the program
variableRename :: Traversable t
               => AnnotationFile                 -- ^ all annotations
               -> t (Module a)                   -- ^ all modules
               -> (AnnotationFile, t (Module a)) -- ^ updated annotations and modules
variableRename af modules = runIdentity $ -- run $ runReader (St mInputs) $
  (,) <$> handleAnnotationFile af <*> traverse handleModule modules
  -- where
  --   mInputs =
  --     foldl' (\mm m -> HM.insert (moduleName m) (inputPorts m) mm) mempty modules
  --   inputPorts Module{..} =
  --     foldl' (\is p -> if isInput p
  --                      then HS.insert (variableName $ portVariable p) is
  --                      else is) mempty ports

handleAnnotationFile :: FD sig m => AnnotationFile -> m AnnotationFile
handleAnnotationFile af = do
  annots' <- HM.traverseWithKey handleModuleAnnotations (af ^. afAnnotations)
  return $ af & afAnnotations .~ annots'

handleModuleAnnotations :: FD sig m => Id -> ModuleAnnotations -> m ModuleAnnotations
handleModuleAnnotations _moduleName ModuleAnnotations{..} = do
  -- mInputs <- asks (HM.lookup moduleName . getModuleInputs)
  let mInputs = Just []
  case mInputs of
    Nothing -> return ModuleAnnotations{..}
    Just _inputs ->
      -- runReader inputs $
      ModuleAnnotations
      <$> handleAnnotations _moduleAnnotations
      <*> traverse handleQualifier _moduleQualifiers
      <*> traverseSet fix _clocks
      <*> return _canInline

handleAnnotations :: FDM sig m => Annotations -> m Annotations
handleAnnotations Annotations{..} =
  Annotations
  <$> traverseSet fix _sources
  <*> traverseSet fix _sinks
  <*> traverseSet fix _initialEquals
  <*> traverseSet fix _alwaysEquals
  <*> traverseSet fix _assertEquals
  <*> traverseSet fix _tagEquals

handleQualifier :: FDM sig m => Qualifier -> m Qualifier
handleQualifier (QImplies v vs) = QImplies <$> fix v <*> traverse fix vs
handleQualifier (QIff v vs)     = QIff <$> fix v <*> traverse fix vs
handleQualifier (QPairs vs)     = QPairs <$> traverse fix vs

handleModule :: FD sig m => Module a -> m (Module a)
handleModule Module{..} = do
  -- inputs <- asks (hmGet 2 moduleName . getModuleInputs)
  -- runReader inputs $
  Module moduleName
    <$> traverse fixPort ports
    <*> traverse fixVariable variables
    <*> traverse (\(v, e) -> (,) <$> fix v <*> fixExpr e) constantInits
    <*> traverse fixStmt gateStmts
    <*> traverse fixAB alwaysBlocks
    <*> traverse (fixMI moduleName) moduleInstances
    <*> return moduleData

fixPort :: FDM sig m => Port -> m Port
fixPort (Input i)  = Input <$> fixVariable i
fixPort (Output o) = Output <$> fixVariable o

fixVariable :: FDM sig m => Variable -> m Variable
fixVariable (Wire v)     = Wire <$> fix v
fixVariable (Register r) = Register <$> fix r

fixStmt :: FDM sig m => Stmt a -> m (Stmt a)
fixStmt Block{..} = Block <$> traverse fixStmt blockStmts <*> return stmtData
fixStmt Assignment{..} =
  Assignment assignmentType
  <$> fixExpr assignmentLhs
  <*> fixExpr assignmentRhs
  <*> return stmtData
fixStmt IfStmt{..} =
  IfStmt
  <$> fixExpr ifStmtCondition
  <*> fixStmt ifStmtThen
  <*> fixStmt ifStmtElse
  <*> return stmtData
fixStmt Skip{..} = return $ Skip{..}

fixExpr :: FDM sig m => Expr a -> m (Expr a)
fixExpr e@Constant{} = return e
fixExpr e@Str{} = return e
fixExpr Variable{..} = do
  varName' <- fix varName
  return $ Variable{varName = varName', ..}
fixExpr UF{..} = UF ufOp <$> traverse fixExpr ufArgs <*> return exprData
fixExpr IfExpr{..} =
  IfExpr
  <$> fixExpr ifExprCondition
  <*> fixExpr ifExprThen
  <*> fixExpr ifExprElse
  <*> return exprData
fixExpr Select{..} =
  Select
  <$> fixExpr selectVar
  <*> traverse fixExpr selectIndices
  <*> return exprData

fixAB :: FDM sig m => AlwaysBlock a -> m (AlwaysBlock a)
fixAB AlwaysBlock{..} =
  AlwaysBlock
  <$> fixEvent abEvent
  <*> fixStmt abStmt
  <*> return abData

fixEvent :: FDM sig m => Event a -> m (Event a)
fixEvent PosEdge{..} = PosEdge <$> fixExpr eventExpr
fixEvent NegEdge{..} = NegEdge <$> fixExpr eventExpr
fixEvent Star        = return Star

fixMI :: FD sig m => Id -> ModuleInstance a -> m (ModuleInstance a)
fixMI _currentModuleName ModuleInstance{..} = do
  -- currentInputs <- asks (hmGet 3 currentModuleName . getModuleInputs)
  -- targetInputs <- asks (hmGet 4 moduleInstanceType . getModuleInputs)
  ports' <-
    foldM
    (\ports (p, e) -> do
        p' <- fix p -- & runReader targetInputs
        e' <- fixExpr e -- & runReader currentInputs
        return $ HM.insert p' e' ports)
    mempty
    (HM.toList moduleInstancePorts)
  return $ ModuleInstance{moduleInstancePorts = ports', ..}

-- fix :: FDM sig m => Id -> m Id
-- fix v = fix' v <$> ask

-- fix' :: Id -> Ids -> Id
-- fix' v inputs =
--   if v `elem` inputs
--   then inputPrefix <> v
--   else nonInputPrefix <> v

fix :: Monad m => Id -> m Id
fix v = return $ varPrefix <> v

traverseSet :: Monad m => (Id -> m Id) -> Ids -> m Ids
traverseSet mi = foldM (\s' i -> (`HS.insert` s') <$> mi i) mempty
