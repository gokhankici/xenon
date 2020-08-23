{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Xenon.Transform.TransitionRelation
  ( transitionRelation
  , val
  , tag
  , transitionRelation'
  , val'
  , tag'
  , ToVarIndex
  ) where

import           Xenon.Language.IR
import           Xenon.Transform.Horn
import           Xenon.Types
import           Xenon.Utils

import           Control.Carrier.State.Strict
import           Control.Effect.Reader
import qualified Control.Effect.Trace as CET
import           Control.Lens
import           Data.Foldable
import qualified Data.HashSet as HS
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Text.Read (readEither)
import           Data.Hashable (Hashable)

type S = Stmt Int
type M = Module Int

type FD sig m = (Has (Reader M) sig m, Has CET.Trace sig m)

transitionRelation :: FD sig m => S -> m HornExpr
transitionRelation s =
  toAnd <$>
  transitionRelationH mempty LeftRun s <*>
  transitionRelationH mempty RightRun s

type PathCond = L (Expr Int)

transitionRelationH :: FD sig m => PathCond -> HornVarRun -> S -> m HornExpr
transitionRelationH conds r stmt =
  case stmt of
    Block {..} ->
      HAnd <$> traverse (transitionRelationH conds r) blockStmts

    Assignment {..} ->
      return $ toAnd
      (val r assignmentLhs `heq`  wcu Value (val r assignmentRhs))
      (tag r assignmentLhs `hiff` wcu Tag (tagWithCond r conds assignmentRhs))
      where wcu = withClockedUpdate assignmentType

    IfStmt {..} -> do
      let conds' = ifStmtCondition <| conds
          hc     = val r ifStmtCondition
          c      = hc `hne` HInt 0
          not_c  = hc `heq` HInt 0
      t <- transitionRelationH conds' r ifStmtThen
      e <- transitionRelationH conds' r ifStmtElse
      return $ HOr $ toAnd c t |:> toAnd not_c e

    Skip {..} ->
      return $ HBool True

ufVal :: HornVarRun -> Id -> HornAppReturnType -> L (Expr Int) -> HornExpr
ufVal r name t es = HApp name t hes
  where
    hes = val r <$> keepVariables es

mkUFName :: Int -> Id
mkUFName n = "uf_noname_" <> T.pack (show n)

val :: HornVarRun -> Expr Int -> HornExpr
val r = \case
  Constant {..} -> parseVerilogInt constantValue
  Variable {..} -> HVar { hVarName   = varName
                        , hVarModule = varModuleName
                        , hVarIndex  = exprData
                        , hVarType   = Value
                        , hVarRun    = r
                        , hThreadId  = 0
                        }
  UF {..}     ->
    let ufName = T.pack $ show ufOp <> show exprData
    in ufVal r ufName HornInt ufArgs
  IfExpr {..} -> HIte { hIteCond = mkHIteCond r ifExprCondition
                      , hIteThen = val r ifExprThen
                      , hIteElse = val r ifExprElse
                      }
  Str {..}    -> notSupported
  Select {..} -> ufVal r name HornInt (selectVar <| selectIndices)
    where name = mkUFName exprData
  VFCall {..} -> error "val should not be called with a verilog function call"

tagWithCond :: HornVarRun -> PathCond -> Expr Int -> HornExpr
tagWithCond r es e =
  case es of
    SQ.Empty -> tag r e
    _        -> ufTag r (es |> e)

ufTag :: HornVarRun -> L (Expr Int) -> HornExpr
ufTag r = HOr . fmap (tag r) . keepVariables

tag :: HornVarRun -> Expr Int -> HornExpr
tag r = \case
  Constant {..} -> HBool False
  Variable {..} -> HVar { hVarName   = varName
                        , hVarModule = varModuleName
                        , hVarIndex  = exprData
                        , hVarType   = Tag
                        , hVarRun    = r
                        , hThreadId  = 0
                        }
  UF {..}     -> ufTag r ufArgs
  IfExpr {..} -> HIte { hIteCond = mkHIteCond r ifExprCondition
                      , hIteThen = ufTag r $ ifExprCondition |:> ifExprThen
                      , hIteElse = ufTag r $ ifExprCondition |:> ifExprElse
                      }
  Str {..}    -> HBool False
  Select {..} -> ufTag r (selectVar <| selectIndices)
  VFCall {..} -> error "tag should not be called with a verilog function call"

heq, hne, hiff :: HornExpr -> HornExpr -> HornExpr
heq  = HBinary HEquals
hne  = HBinary HNotEquals
hiff = HBinary HIff

-- | make the condition to be used for the horn expressions from the IR
mkHIteCond :: HornVarRun -> Expr Int -> HornExpr
mkHIteCond r c = val r c `hne` HInt 0

-- type Exprs = HS.HashSet (Expr Int)
{- |
Given a list of expressions, this returns a list of variables that appear in the
expressions without any duplicates.
-}
keepVariables :: (Eq a, Hashable a) => L (Expr a) -> L (Expr a)
keepVariables es = goEs es & evalState HS.empty & run
  where
    goE :: (Eq a, Hashable a, Algebra sig m)
        => Expr a
        -> StateC (HS.HashSet (Expr a)) m (L (Expr a))
    goE Constant{..}   = return mempty
    goE v@Variable{..} = do hasVar <- gets $ HS.member v
                            if hasVar
                              then return mempty
                              else do modify $ HS.insert v
                                      return $ SQ.singleton v
    goE UF{..}         = goEs ufArgs
    goE IfExpr{..}     = goEs $ ifExprCondition |:> ifExprThen |> ifExprElse
    goE Str{..}        = return mempty
    goE Select{..}     = goEs $ selectVar <| selectIndices
    goE VFCall{..}     = error "keepVariables should not be called with a verilog function call"

    goEs :: (Eq a, Hashable a, Algebra sig m)
         => L (Expr a)
         -> StateC (HS.HashSet (Expr a)) m (L (Expr a))
    goEs = fmap (foldl' (<>) mempty) . traverse goE


parseVerilogInt :: Id -> HornExpr
parseVerilogInt value = case readEither v' of
  Left  _ -> HConstant value
  Right n -> HInt n
 where
  v  = T.unpack value
  v' = case v of
    '0' : 'b' : rst -> rst
    _               -> v

toAnd :: HornExpr -> HornExpr -> HornExpr
toAnd e1 e2 = HAnd $ mempty |> e1 |> e2

-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

type ToVarIndex = Id -> Int

transitionRelation' :: (FD sig m, ShowIndex a) => ToVarIndex -> Stmt a -> m HornExpr
transitionRelation' toVarIndex s =
  toAnd <$>
  transitionRelationH' toVarIndex mempty LeftRun s <*>
  transitionRelationH' toVarIndex mempty RightRun s

transitionRelationH' :: (FD sig m, ShowIndex a) => ToVarIndex -> L (Expr a) -> HornVarRun -> Stmt a -> m HornExpr
transitionRelationH' toVarIndex conds r stmt =
  case stmt of
    Block {..} ->
      HAnd <$> traverse (transitionRelationH' toVarIndex conds r) blockStmts

    Assignment {..} ->
      return $ toAnd
      (val' toVarIndex r assignmentLhs `heq`  wcu Value (val' toVarIndex r assignmentRhs))
      (tag' toVarIndex r assignmentLhs `hiff` wcu Tag (tagWithCond' toVarIndex r conds assignmentRhs))
      where wcu = withClockedUpdate assignmentType

    IfStmt {..} -> do
      let conds' = ifStmtCondition <| conds
          hc     = val' toVarIndex r ifStmtCondition
          c      = hc `hne` HInt 0
          not_c  = hc `heq` HInt 0
      t <- transitionRelationH' toVarIndex conds' r ifStmtThen
      e <- transitionRelationH' toVarIndex conds' r ifStmtElse
      return $ HOr $ toAnd c t |:> toAnd not_c e

    Skip {..} ->
      return $ HBool True

tagWithCond' :: ShowIndex a => ToVarIndex -> HornVarRun -> L (Expr a) -> Expr a -> HornExpr
tagWithCond' toVarIndex r es e =
  case es of
    SQ.Empty -> tag' toVarIndex r e
    _        -> ufTag' toVarIndex r (es |> e)

val' :: ShowIndex a => ToVarIndex -> HornVarRun -> Expr a -> HornExpr
val' toVarIndex r = \case
  Constant {..} -> parseVerilogInt constantValue
  Variable {..} -> HVar { hVarName   = varName
                        , hVarModule = varModuleName
                        , hVarIndex  = toVarIndex varName
                        , hVarType   = Value
                        , hVarRun    = r
                        , hThreadId  = 0
                        }
  UF {..} ->
    let ufName = T.pack $ show ufOp <> show exprData
    in ufVal' toVarIndex r ufName HornInt ufArgs
  IfExpr {..} -> HIte { hIteCond = mkHIteCond' toVarIndex r ifExprCondition
                      , hIteThen = val' toVarIndex r ifExprThen
                      , hIteElse = val' toVarIndex r ifExprElse
                      }
  Str {..}    -> notSupported
  Select {..} -> ufVal' toVarIndex r name HornInt (selectVar <| selectIndices)
    where name = mkUFName' exprData
  VFCall {..} -> error "val should not be called with a verilog function call"

ufVal' :: ShowIndex a => ToVarIndex -> HornVarRun -> Id -> HornAppReturnType -> L (Expr a) -> HornExpr
ufVal' toVarIndex r name t es = HApp name t hes
  where
    hes = val' toVarIndex r <$> keepVariables es

mkHIteCond' :: ShowIndex a => ToVarIndex -> HornVarRun -> Expr a -> HornExpr
mkHIteCond' toVarIndex r c = val' toVarIndex r c `hne` HInt 0

mkUFName' :: ShowIndex a => a -> Id
mkUFName' n = "uf_noname_" <> T.pack (show n)

tag' :: ShowIndex a => ToVarIndex -> HornVarRun -> Expr a -> HornExpr
tag' toVarIndex r = \case
  Constant {..} -> HBool False
  Variable {..} -> HVar { hVarName   = varName
                        , hVarModule = varModuleName
                        , hVarIndex  = toVarIndex varName
                        , hVarType   = Tag
                        , hVarRun    = r
                        , hThreadId  = 0
                        }
  UF {..}     -> ufTag' toVarIndex r ufArgs
  IfExpr {..} -> HIte { hIteCond = mkHIteCond' toVarIndex r ifExprCondition
                      , hIteThen = ufTag' toVarIndex r $ ifExprCondition |:> ifExprThen
                      , hIteElse = ufTag' toVarIndex r $ ifExprCondition |:> ifExprElse
                      }
  Str {..}    -> HBool False
  Select {..} -> ufTag' toVarIndex r (selectVar <| selectIndices)
  VFCall {..} -> error "tag should not be called with a verilog function call"

ufTag' :: ShowIndex a => ToVarIndex -> HornVarRun -> L (Expr a) -> HornExpr
ufTag' toVarIndex r = HOr . fmap (tag' toVarIndex r) . keepVariables


withClockedUpdate :: AssignmentType -> HornVarType -> HornExpr -> HornExpr
withClockedUpdate asgnType _ arg | asgnType /= NonBlocking = arg
withClockedUpdate _ t arg =
  HApp { hAppFun  = fn
       , hAppRet  = rt
       , hAppArgs = return arg
       }
  where
    (rt, fn) =
       case t of
         Tag   -> (HornBool, "xenon_clock_tag")
         Value -> (HornInt , "xenon_clock_value")
