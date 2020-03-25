{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module Iodine.Transform.VariableRename
  ( variableRename
  , inputPrefix
  , nonInputPrefix
  ) where

import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Polysemy
import           Polysemy.Reader

newtype St = St { getModuleInputs :: HM.HashMap Id Ids }

type FD a r  = Members '[Reader St] r
type FDM a r = (FD a r, Members '[Reader Ids] r)

inputPrefix, nonInputPrefix :: Id
inputPrefix    = "I_"
nonInputPrefix = "NI_"

-- | renames all the variables in the program to aid the speed of verification
variableRename :: Traversable t
               => AnnotationFile                 -- ^ all annotations
               -> t (Module a)                   -- ^ all modules
               -> (AnnotationFile, t (Module a)) -- ^ updated annotations and modules
variableRename af modules = run $ runReader (St mInputs) $
  (,) <$> handleAnnotationFile af <*> traverse handleModule modules
  where
    mInputs =
      foldl' (\mm m -> HM.insert (moduleName m) (inputPorts m) mm) mempty modules
    inputPorts Module{..} =
      foldl' (\is p -> if isInput p
                       then HS.insert (variableName $ portVariable p) is
                       else is) mempty ports

handleAnnotationFile :: FD a r => AnnotationFile -> Sem r AnnotationFile
handleAnnotationFile af = do
  annots' <- HM.traverseWithKey handleModuleAnnotations (af ^. afAnnotations)
  return $ af & afAnnotations .~ annots'

handleModuleAnnotations :: FD a r => Id -> ModuleAnnotations -> Sem r ModuleAnnotations
handleModuleAnnotations moduleName ModuleAnnotations{..} = do
  inputs <- asks (hmGet 1 moduleName . getModuleInputs)
  runReader inputs $
    ModuleAnnotations
    <$> handleAnnotations _moduleAnnotations
    <*> traverse handleQualifier _moduleQualifiers
    <*> traverseSet fix _clocks

handleAnnotations :: FDM a r => Annotations -> Sem r Annotations
handleAnnotations Annotations{..} =
  Annotations
  <$> traverseSet fix _sources
  <*> traverseSet fix _sinks
  <*> traverseSet fix _initialEquals
  <*> traverseSet fix _alwaysEquals
  <*> traverseSet fix _assertEquals
  <*> traverseSet fix _tagEquals

handleQualifier :: FDM a r => Qualifier -> Sem r Qualifier
handleQualifier (QImplies v vs) = QImplies <$> fix v <*> traverse fix vs
handleQualifier (QIff v vs)     = QIff <$> fix v <*> traverse fix vs
handleQualifier (QPairs vs)     = QPairs <$> traverse fix vs

handleModule :: FD a r => Module a -> Sem r (Module a)
handleModule Module{..} = do
  inputs <- asks (hmGet 2 moduleName . getModuleInputs)
  moduleInstances' <- traverse (fixMI moduleName) moduleInstances
  runReader inputs $
    Module moduleName
    <$> traverse fixPort ports
    <*> traverse fixVariable variables
    <*> traverse fixStmt gateStmts
    <*> traverse fixAB alwaysBlocks
    <*> return moduleInstances'
    <*> return moduleData

fixPort :: FDM a r => Port -> Sem r Port
fixPort (Input i)  = Input <$> fixVariable i
fixPort (Output o) = Output <$> fixVariable o

fixVariable :: FDM a r => Variable -> Sem r Variable
fixVariable (Wire v)     = Wire <$> fix v
fixVariable (Register r) = Register <$> fix r

fixStmt :: FDM a r => Stmt a -> Sem r (Stmt a)
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

fixExpr :: FDM a r => Expr a -> Sem r (Expr a)
fixExpr Constant{..} = return $ Constant{..}
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
fixExpr Str{..} = return $ Str{..}
fixExpr Select{..} =
  Select
  <$> fixExpr selectVar
  <*> traverse fixExpr selectIndices
  <*> return exprData

fixAB :: FDM a r => AlwaysBlock a -> Sem r (AlwaysBlock a)
fixAB AlwaysBlock{..} =
  AlwaysBlock
  <$> fixEvent abEvent
  <*> fixStmt abStmt
  <*> return abData

fixEvent :: FDM a r => Event a -> Sem r (Event a)
fixEvent PosEdge{..} = PosEdge <$> fixExpr eventExpr
fixEvent NegEdge{..} = NegEdge <$> fixExpr eventExpr
fixEvent Star        = return Star

fixMI :: FD a r => Id -> ModuleInstance a -> Sem r (ModuleInstance a)
fixMI currentModuleName ModuleInstance{..} = do
  currentInputs <- asks (hmGet 3 currentModuleName . getModuleInputs)
  targetInputs <- asks (hmGet 4 moduleInstanceType . getModuleInputs)
  ports' <-
    foldM
    (\ports (p, e) -> do
        p' <- fix p & runReader targetInputs
        e' <- fixExpr e & runReader currentInputs
        return $ HM.insert p' e' ports)
    mempty
    (HM.toList moduleInstancePorts)
  return $ ModuleInstance{moduleInstancePorts = ports', ..}

fix :: FDM a r => Id -> Sem r Id
fix v = fix' v <$> ask

fix' :: Id -> Ids -> Id
fix' v inputs =
  if v `elem` inputs
  then inputPrefix <> v
  else nonInputPrefix <> v

traverseSet :: (Id -> Sem r Id) -> Ids -> Sem r Ids
traverseSet mi = foldM (\s' i -> (`HS.insert` s') <$> mi i) mempty
