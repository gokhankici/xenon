{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
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

import           Control.Lens
import           Control.Monad
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap as IM
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Polysemy
import           Polysemy.Error
import           Polysemy.Reader
import           Polysemy.State
import           Polysemy.Trace


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
normalize :: Members '[Trace, Error IodineException] r
          => L (Module Int) -> Sem r NormalizeOutput
normalize modules = traverse normalizeModule modules <* trace "SSA DONE!" & runNormalize

-- | Run normalize on all the statements inside the given module.
normalizeModule :: FD r => Module Int -> Sem r (Module Int)
normalizeModule Module {..} = runReader (ModuleName moduleName) $ do
  unless (SQ.null gateStmts) $
    throw $ IE Normalize "gateStmts should be empty here"
  Module moduleName ports variables
    <$> return mempty
    <*> traverse normalizeAB alwaysBlocks
    <*> traverse normalizeModuleInstance moduleInstances
    <*> return moduleData

-- | Run normalize on all the statements inside the given always block.
normalizeAB :: FDM r => AlwaysBlock Int -> Sem r (AlwaysBlock Int)
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
normalizeEvent :: FD r => Event a -> Sem r (Event Int)
normalizeEvent =
  -- normalizing event does not require statement state
  runReader initialStmtSt . \case
  PosEdge {..} -> PosEdge <$> normalizeExpr eventExpr
  NegEdge {..} -> NegEdge <$> normalizeExpr eventExpr
  Star         -> return Star

-- | Normalize a module instance. This just assigns zero to the expressions that
-- appear in port assignments.
normalizeModuleInstance :: FD r => ModuleInstance Int -> Sem r (ModuleInstance Int)
normalizeModuleInstance ModuleInstance{..} = do
  ports' <- traverse normalizeExpr moduleInstancePorts & runReader initialStmtSt
  return $ ModuleInstance {moduleInstancePorts = ports', ..}


-- #############################################################################

{- |
This function should be used to normalize the top level statements. For
statements that appear inside the code block, use 'normalizeStmt'.
-}
normalizeStmtTop :: FDM r => AlwaysBlock Int -> Sem r (Stmt Int)
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
normalizeStmt :: FDS r => Stmt Int -> Sem r (Stmt Int)
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
    normalizeStmtExpr :: FDS r => Expr a -> Sem r (Expr Int)
    normalizeStmtExpr e = do
      stmtSt <- get @StmtSt
      normalizeExpr e & runReader stmtSt

{- |
Normalizes the given branches using the current state. If the variables are
updated differently, extra assignments are added to the corresponding branches.
This way, the id of the variable that represents the current value becomes equal
in both sides.
-}
normalizeBranches :: FDS r
                  => Stmt Int                   -- ^ then branch
                  -> Stmt Int                   -- ^ else branch
                  -> Sem r (Stmt Int, Stmt Int) -- ^ normalized then & else branches
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
balanceBranches :: FDM r
                => AssignmentType
                -> (VarId, VarId) -- ^ variable id maps of the branches
                -> Sem r BBResult -- ^ merged variable id map, and extra
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
normalizeExpr :: FDR r => Expr a -> Sem r (Expr Int)
normalizeExpr = \case
  Constant {..} -> Constant constantValue <$> freshId ExprId

  Variable {..} -> Variable varName varModuleName <$> getLastBlocking varName

  UF {..} -> do
    args <- traverse normalizeExpr ufArgs
    n    <- freshId FunId
    let name = "uf_" <> ufName <> "_" <> T.pack (show n)
    return $ UF name args n

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


-- #############################################################################

type FD r   = Members '[State St, Trace, Error IodineException] r
type FDR r  = (FD r, Members '[Reader StmtSt] r)
type FDM r  = (FD r, Members '[Reader ModuleName] r)
type FDS r  = (FDM r, Members '[State StmtSt] r)

newtype ModuleName = ModuleName { getModuleName :: Id }

initialSt :: St
initialSt = St 0 0 mempty

initialStmtSt :: StmtSt
initialStmtSt = StmtSt mempty mempty mempty

runNormalize :: Sem (State St ': r) a -> Sem r (a, TRSubs)
runNormalize act = do
  (st, res) <- act & runState initialSt
  return (res, st ^. trSubs)

-- | give fresh id to each thread and module
-- 0 is assigned to each stmt
assignThreadIds :: Traversable t => t (Module a) -> t (Module Int)
assignThreadIds modules =
  run $ evalState 0 $ traverse freshModule modules
  where
    getFreshId :: Members '[State Int] r => Sem r Int
    getFreshId = get <* modify (+ 1)

    freshModule :: Members '[State Int] r => Module a -> Sem r (Module Int)
    freshModule Module{..} =
      Module moduleName ports variables
      <$> traverse freshStmt gateStmts
      <*> traverse freshAB alwaysBlocks
      <*> traverse freshMI moduleInstances
      <*> getFreshId

    freshStmt :: Members '[State Int] r => Stmt a -> Sem r (Stmt Int)
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

    freshAB :: Members '[State Int] r => AlwaysBlock a -> Sem r (AlwaysBlock Int)
    freshAB AlwaysBlock{..} =
      AlwaysBlock (0 <$ abEvent) <$> freshStmt abStmt <*> getFreshId

    freshMI :: Members '[State Int] r => ModuleInstance a -> Sem r (ModuleInstance Int)
    freshMI ModuleInstance{..} =
      ModuleInstance
      moduleInstanceType moduleInstanceName
      (HM.map (0 <$) moduleInstancePorts)
      <$> getFreshId

data IdType = FunId | ExprId

freshId :: FD r => IdType -> Sem r Int
freshId = \case
  -- modules, always blocks and statements share the same counter
  FunId  -> incrCount funId
  ExprId -> incrCount exprId
  where
    incrCount :: FD r => Lens St St Int Int -> Sem r Int
    incrCount l = gets (^. l) <* modify (l +~ 1)

freshVariable :: FDS r => Expr a -> Sem r (Expr Int)
freshVariable var = do
  modify $ varMaxIds %~ HM.alter (Just . maybe 1 (+ 1)) name
  Variable name (varModuleName var) <$> gets (^. varMaxIds . to (HM.! name))
  where
    name = varName var

getLastBlocking :: FDR r => Id -> Sem r Int
getLastBlocking name =
  asks @StmtSt (^. lastBlocking . to (HM.lookupDefault 0 name))

updateLastBlocking :: FDS r => Expr Int -> Sem r ()
updateLastBlocking var =
  modify $ lastBlocking %~ HM.insert name varId
  where
    name  = varName var
    varId = exprData var

updateLastNonBlocking :: FDS r => Expr Int -> Sem r ()
updateLastNonBlocking var =
  modify $ lastNonBlocking %~ HM.insert name varId
  where
    name  = varName var
    varId = exprData var
