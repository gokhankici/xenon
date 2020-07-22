{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Transform.Normalize
  ( normalize
  , assignThreadIds
  , NormalizeOutput
  , NormalizeIR
  )
where

import           Iodine.Language.IR
import           Iodine.Types

import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Effect.Error
import           Control.Lens
import           Control.Monad
import           Data.Functor
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap as IM
import qualified Data.Sequence as SQ


-- #############################################################################

type NormalizeIR     = L (Module Int)
type NormalizeOutput = (NormalizeIR, TRSubs)

type VarId  = HM.HashMap Id Int
type TRSubs = IM.IntMap VarId

-- | Global state
data St =
  St { _exprId :: Int    -- ^ counter for statements
     , _funId  :: Int    -- ^ counter for functions
     , _trSubs :: TRSubs -- ^ This substitution map is used to determine the
                         -- kvar in the head position of the horn clauses. Has
                         -- type (stmt -> var -> var index)
     }

-- | State only relevant to assignments
data StmtSt =
  StmtSt { _varMaxIds       :: VarId  -- ^ counter for variables
         , _lastBlocking    :: VarId  -- ^ last blocking assignment of the vars
         , _lastNonBlocking :: VarId  -- ^ non blocking assignments of the vars
         }

makeLenses ''St
makeLenses ''StmtSt

type FD sig m  = (Has (State St) sig m) --, Effect sig)
type FDM sig m = (FD sig m, Has (Reader ModuleName) sig m, Has (Reader VFM) sig m)
type FDS sig m = (FDM sig m, Has (State StmtSt) sig m)
type FDR sig m = (FDM sig m, Has (Reader StmtSt) sig m)

newtype ModuleName = ModuleName { getModuleName :: Id }
type VFM = HM.HashMap Id (VerilogFunction Int)

-- #############################################################################

{- |
This pass is used to make verification condition generation easier by:

1. Each new variable, statement, and always block within a module will have an
unique id. Index 0 corresponds to the initial value of a variable.

2. It balances the assignments to variables. For example, if a variable is
assigned only in one of the branches of an if statement, the missing assignment
is added to the corresponding branch. This way the substitutions that implement
the transition relation in the kvars become simple.
-}
normalize :: (Has (Error IodineException) sig m) --, Effect sig)
          => L (Module Int) -> m NormalizeOutput
normalize modules = traverse normalizeModule modules & runNormalize

-- | Run normalize on all the statements inside the given module.
normalizeModule :: (FD sig m, Has (Error IodineException) sig m)
                => Module Int -> m (Module Int)
normalizeModule Module {..} = runReader (ModuleName moduleName) $ runReader verilogFunctions $ do
  unless (SQ.null gateStmts) $
    throwError $ IE Normalize "gateStmts should be empty here"
  Module moduleName ports variables constantInits verilogFunctions
    <$> return mempty
    <*> traverse normalizeAB alwaysBlocks
    <*> traverse normalizeModuleInstance moduleInstances
    <*> return moduleData

-- | Run normalize on all the statements inside the given always block.
normalizeAB :: FDM sig m => AlwaysBlock Int -> m (AlwaysBlock Int)
normalizeAB ab@AlwaysBlock{..} = do
  abEvent' <- normalizeEvent abEvent
  abStmt' <- normalizeStmtTop ab
  return $
    AlwaysBlock { abEvent = abEvent'
                , abStmt  = abStmt'
                , ..
                }

-- | Normalize the event of an always block. This just assigns zero to the
-- expressions that appear under an event.
normalizeEvent :: FDM sig m => Event a -> m (Event Int)
normalizeEvent =
  -- normalizing event does not require statement state
  runReader initialStmtSt . \case
  PosEdge {..} -> PosEdge <$> normalizeExpr eventExpr
  NegEdge {..} -> NegEdge <$> normalizeExpr eventExpr
  Star         -> return Star

-- | Normalize a module instance. This just assigns zero to the expressions that
-- appear in port assignments.
normalizeModuleInstance :: FDM sig m => ModuleInstance Int -> m (ModuleInstance Int)
normalizeModuleInstance ModuleInstance{..} = do
  ports' <- traverse normalizeExpr moduleInstancePorts & runReader initialStmtSt
  return $ ModuleInstance {moduleInstancePorts = ports', ..}

-- #############################################################################

{- |
This function should be used to normalize the top level statements. For
statements that appear inside the code block, use 'normalizeStmt'.
-}
normalizeStmtTop :: FDM sig m => AlwaysBlock Int -> m (Stmt Int)
normalizeStmtTop ab = do
  (stmtSt, stmt') <- normalizeStmt (abStmt ab) & runState initialStmtSt
  let stmtSubs = HM.union (stmtSt ^. lastBlocking) (stmtSt ^. lastNonBlocking)
  modify $ trSubs %~ IM.insert (getData ab) stmtSubs
  return stmt'

{- |
Normalizes the given statement.

* When normalizing an assignment, the value of the last blocking assignment is
  used for the rhs.
* The same is true when normalizing the conditional of an if statement.
* 'normalizeBranches' implements the most of the logic needed to normalize if
  conditions.
-}
normalizeStmt :: FDS sig m => Stmt Int -> m (Stmt Int)
normalizeStmt = \case
  Block {..} ->
    Block <$> traverse normalizeStmt blockStmts <*> return stmtData

  Assignment {..} -> do
    lhs' <- freshVariable assignmentLhs
    rhs' <- normalizeStmtExpr assignmentRhs
    case assignmentType of
      Continuous  -> updateLastBlocking lhs'
      Blocking    -> updateLastBlocking lhs'
      NonBlocking -> updateLastNonBlocking lhs'
    Assignment assignmentType lhs' rhs' <$> return stmtData

  IfStmt {..} -> do
    cond' <- normalizeStmtExpr ifStmtCondition
    (then', else') <- normalizeBranches ifStmtThen ifStmtElse
    IfStmt cond' then' else' <$> return stmtData

  Skip{..} -> return $ Skip{..}

  where
    normalizeStmtExpr :: FDS sig m => Expr a -> m (Expr Int)
    normalizeStmtExpr e = do
      stmtSt <- get @StmtSt
      normalizeExpr e & runReader stmtSt

{- |
Normalizes the given branches using the current state. If the variables are
updated differently, extra assignments are added to the corresponding branches.
This way, the id of the variable that represents the current value becomes equal
in both sides.
-}
normalizeBranches :: FDS sig m
                  => Stmt Int                   -- ^ then branch
                  -> Stmt Int                   -- ^ else branch
                  -> m (Stmt Int, Stmt Int) -- ^ normalized then & else branches
normalizeBranches thenS elseS = do
  stInit <- get @StmtSt
  thenS' <- normalizeStmt thenS
  thenSt <- get @StmtSt
  put stInit
  elseS' <- normalizeStmt elseS
  elseSt <- get @StmtSt
  (newLastBlocking, thenExtraBlockingStmts, elseExtraBlockingStmts) <-
    balanceBranches Blocking ( thenSt ^. lastBlocking
                             , elseSt ^. lastBlocking)
  (newLastNonBlocking, thenExtraNonBlockingStmts, elseExtraNonBlockingStmts) <-
    balanceBranches NonBlocking ( thenSt ^. lastNonBlocking
                                , elseSt ^. lastNonBlocking)
  let newVarMaxIds = HM.unionWith max (thenSt ^. varMaxIds) (elseSt ^. varMaxIds)
  modify $
    (varMaxIds .~ newVarMaxIds) .
    (lastBlocking .~ newLastBlocking) .
    (lastNonBlocking .~ newLastNonBlocking)
  (,)
    <$> extendStmt thenS' (thenExtraBlockingStmts <> thenExtraNonBlockingStmts)
    <*> extendStmt elseS' (elseExtraBlockingStmts <> elseExtraNonBlockingStmts)
  where
    extendStmt stmt extraStmts =
      case extraStmts of
        SQ.Empty -> return stmt
        _        -> return $ Block (stmt <| extraStmts) 0

{- |
This is the helper method used by 'normalizeBranches'. Since the merge of
blocking and non-blocking maps are almost the same, this function is used to
implement both of them.
-}
type BBResult = (VarId, L (Stmt Int), L (Stmt Int))
balanceBranches :: FDM sig m
                => AssignmentType
                -> (VarId, VarId) -- ^ variable id maps of the branches
                -> m BBResult -- ^ merged variable id map, and extra
                                  -- assignment statements needed for the
                                  -- branches
balanceBranches t (varMap1, varMap2) = do
  modName <- asks getModuleName
  let mkStmt (v, mergedNo, foundNo) =
        Assignment t
        (Variable v modName mergedNo) -- lhs
        (Variable v modName foundNo)  -- rhs
        0
  let createExtraStatements = fmap mkStmt . findMissing
  return (mergedMap, createExtraStatements varMap1, createExtraStatements varMap2)
  where
    mergedMap = varMap1 `merge` varMap2
    merge = HM.unionWith max

    -- This helper function computes the difference between the merged map and
    -- the initial argument of the function. varMap is either varMap1 or
    -- varMap2.
    findMissing varMap =
      HM.foldlWithKey' go SQ.empty mergedMap
      where
        go acc var mergedNo =
          let foundNo = HM.lookupDefault 0 var varMap
          in if | mergedNo >  foundNo -> acc |> (var, mergedNo, foundNo)
                | mergedNo == foundNo -> acc
                | otherwise           -> error "expected (mergedNo >= foundNo)"


-- #############################################################################

{- |
Normalizes the expression. It assigns the index of the last non-blocking
assignment to the variables, and zero for the rest of the expression types. It
-}
normalizeExpr :: FDR sig m => Expr a -> m (Expr Int)
normalizeExpr = \case
  Constant {..} -> Constant constantValue <$> freshId ExprId

  Variable {..} -> Variable varName varModuleName <$> getLastBlocking varName

  UF {..} ->
    UF ufOp
    <$> traverse normalizeExpr ufArgs
    <*> freshId FunId

  IfExpr {..} ->
    IfExpr
    <$> normalizeExpr ifExprCondition
    <*> normalizeExpr ifExprThen
    <*> normalizeExpr ifExprElse
    <*> freshId ExprId

  Str {..} -> Str strValue <$> freshId ExprId

  Select {..} ->
    Select
    <$> normalizeExpr selectVar
    <*> traverse normalizeExpr selectIndices
    <*> freshId ExprId

  VFCall {..} ->
    VFCall vfCallFunction
    <$> traverse normalizeExpr vfCallArgs
    <*> freshId ExprId
    >>= inlineVerilogFunction

-- #############################################################################

initialSt :: St
initialSt = St 0 0 mempty

initialStmtSt :: StmtSt
initialStmtSt = StmtSt mempty mempty mempty

runNormalize :: Monad m => StateC St m a -> m (a, TRSubs)
runNormalize act = do
  (st, res) <- act & runState initialSt
  return (res, st ^. trSubs)

-- | give fresh id to each thread, module and verilog functions
-- 0 is assigned to each stmt
assignThreadIds :: Traversable t => t (Module a) -> t (Module Int)
assignThreadIds modules =
  run $ evalState @Int 0 $ traverse freshModule modules
  where
    getFreshId = get <* modify @Int (+ 1)

    freshModule Module{..} =
      Module moduleName ports variables
      (fmap ($> 0) <$> constantInits)
      <$> traverse freshF verilogFunctions
      <*> traverse freshStmt gateStmts
      <*> traverse freshAB alwaysBlocks
      <*> traverse freshMI moduleInstances
      <*> getFreshId

    freshStmt Block{..} =
      Block <$> traverse freshStmt blockStmts <*> return 0
    freshStmt Assignment{..} =
      return $
      Assignment assignmentType (0 <$ assignmentLhs) (0 <$ assignmentRhs) 0
    freshStmt IfStmt{..} =
      IfStmt (0 <$ ifStmtCondition)
      <$> freshStmt ifStmtThen
      <*> freshStmt ifStmtElse
      <*> return 0
    freshStmt Skip{} = return $ Skip 0

    freshAB AlwaysBlock{..} =
      AlwaysBlock (0 <$ abEvent) <$> freshStmt abStmt <*> getFreshId

    freshMI ModuleInstance{..} =
      ModuleInstance
      moduleInstanceType moduleInstanceName
      (HM.map (0 <$) moduleInstancePorts)
      <$> getFreshId

    freshF VerilogFunction{..} =
      VerilogFunction verilogFunctionName verilogFunctionPorts
      (0 <$ verilogFunctionExpr)
      <$> getFreshId

data IdType = FunId | ExprId

freshId :: FD sig m => IdType -> m Int
freshId = \case
  -- modules, always blocks and statements share the same counter
  FunId  -> incrCount funId
  ExprId -> incrCount exprId
  where
    incrCount :: FD sig m => Lens St St Int Int -> m Int
    incrCount l = gets (^. l) <* modify (l +~ 1)

freshVariable :: FDS sig m => Expr a -> m (Expr Int)
freshVariable var = do
  modify $ varMaxIds %~ HM.alter (Just . maybe 1 (+ 1)) name
  Variable name (varModuleName var) <$> gets (^. varMaxIds . to (HM.! name))
  where
    name = varName var

getLastBlocking :: FDR sig m => Id -> m Int
getLastBlocking name =
  asks @StmtSt (^. lastBlocking . to (HM.lookupDefault 0 name))

updateLastBlocking :: FDS sig m => Expr Int -> m ()
updateLastBlocking var =
  modify $ lastBlocking %~ HM.insert name varId
  where
    name  = varName var
    varId = exprData var

updateLastNonBlocking :: FDS sig m => Expr Int -> m ()
updateLastNonBlocking var =
  modify $ lastNonBlocking %~ HM.insert name varId
  where
    name  = varName var
    varId = exprData var

inlineVerilogFunction :: FDM sig m => Expr Int -> m (Expr Int)
inlineVerilogFunction VFCall {..} = do
  VerilogFunction{..} <- (HM.! vfCallFunction) <$> ask @VFM
  toBeReplaced <-
    toList . SQ.zip verilogFunctionPorts <$>
    traverse inlineVerilogFunction vfCallArgs
  replaceVar toBeReplaced <$>
    inlineVerilogFunction verilogFunctionExpr
inlineVerilogFunction e@Constant{} = return e
inlineVerilogFunction e@Variable{} = return e
inlineVerilogFunction e@Str{}      = return e
inlineVerilogFunction UF{..} =
  UF ufOp
  <$> traverse inlineVerilogFunction ufArgs
  <*> return exprData
inlineVerilogFunction IfExpr{..} =
  IfExpr
  <$> inlineVerilogFunction ifExprCondition
  <*> inlineVerilogFunction ifExprThen
  <*> inlineVerilogFunction ifExprElse
  <*> return exprData
inlineVerilogFunction Select{..} =
  Select selectVar
  <$> traverse  inlineVerilogFunction selectIndices
  <*> return exprData

replaceVar :: [(Id, Expr Int)] -> Expr Int -> Expr Int
replaceVar vs = go
  where
    go e@Variable{..} =
      case lookup varName vs of
        Nothing -> e
        Just e' -> e'
    go VFCall{}           = error "replaceVar should not be called with VFCall"
    go e@Constant{}       = e
    go e@Str{}            = e
    go UF{..}             = UF ufOp (go <$> ufArgs) exprData
    go (IfExpr c e1 e2 a) = IfExpr (go c) (go e1) (go e2) a
    go (Select v is a)    = Select (go v) (go <$> is) a