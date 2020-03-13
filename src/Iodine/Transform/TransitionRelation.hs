{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Transform.TransitionRelation
  ( transitionRelation
  , val
  , tag
  ) where

import           Iodine.Language.IR
import           Iodine.Transform.Horn
import           Iodine.Types
import           Iodine.Utils

import           Control.Lens
import           Data.Foldable
import qualified Data.HashSet as HS
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Polysemy
import           Polysemy.State
import           Text.Read (readEither)

type S = Stmt Int

transitionRelation :: S -> HornExpr
transitionRelation s =
  HAnd $
  transitionRelation' mempty LeftRun s |:>
  transitionRelation' mempty RightRun s

type PathCond = L (Expr Int)

transitionRelation' :: PathCond -> HornVarRun -> S -> HornExpr
transitionRelation' conds r stmt =
  case stmt of
    Block {..} ->
      HAnd $ transitionRelation' conds r <$> blockStmts

    Assignment {..} ->
      HAnd $
      (val r assignmentLhs `heq` val r assignmentRhs) |:>
      (tag r assignmentLhs `hiff` tagWithCond r conds assignmentRhs)

    IfStmt {..} ->
      let conds' = ifStmtCondition <| conds
          hc     = val r ifStmtCondition
          c      = hc `heq` HInt 0
          not_c  = HBinary HNotEquals hc (HInt 0)
          t      = transitionRelation' conds' r ifStmtThen
          e      = transitionRelation' conds' r ifStmtElse
      in  HOr $ HAnd (c |:> t) |:> HAnd (not_c |:> e)

    Skip {..} ->
      HBool True

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
  UF {..}     -> ufVal r ufName HornInt ufArgs
  IfExpr {..} -> ufVal r name HornInt (ifExprCondition |:> ifExprThen |> ifExprElse)
    where name = mkUFName exprData
  Str {..}    -> notSupported
  Select {..} -> ufVal r name HornInt (selectVar <| selectIndices)
    where name = mkUFName exprData

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
  IfExpr {..} -> ufTag r (ifExprCondition |:> ifExprThen |> ifExprElse)
  Str {..}    -> HBool False
  Select {..} -> ufTag r (selectVar <| selectIndices)

heq, hiff :: HornExpr -> HornExpr -> HornExpr
heq  = HBinary HEquals
hiff = HBinary HIff

{- |
Given a list of expressions, this returns a list of variables that appear in the
expressions without any duplicates.
-}
keepVariables :: L (Expr Int) -> L (Expr Int)
keepVariables es = goEs es & evalState HS.empty & run
  where
    goE :: Member (State (HS.HashSet (Expr Int))) r
        => Expr Int
        -> Sem r (L (Expr Int))
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

    goEs :: Member (State (HS.HashSet (Expr Int))) r
         => L (Expr Int)
         -> Sem r (L (Expr Int))
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
