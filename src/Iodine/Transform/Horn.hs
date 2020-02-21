{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Iodine.Transform.Horn where

import           Iodine.Language.IR
import qualified Iodine.Language.IR as IIR
import           Iodine.Types

import           Control.DeepSeq
import           Data.Foldable
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           GHC.Generics
import qualified Language.Fixpoint.Types as FT
import qualified Text.PrettyPrint as PP

data Horn a =
       Horn { hornHead   :: HornExpr
            , hornBody   :: HornExpr
            , hornType   :: HornType
            , hornStmtId :: Int
            , hornData   :: a
            }
       deriving (Show, Functor)


data HornBinaryOp = HEquals | HNotEquals | HImplies | HIff

data HornType = Init
              | TagReset
              | SourceReset
              | Next
              | TagEqual
              | Interference
              | AssertEqCheck
              | WellFormed
              | InstanceCheck
              | ModuleSummary
              deriving (Eq, Show, Generic)

data HornVarType = Tag | Value
                   deriving (Eq, Show)

data HornVarRun  = LeftRun | RightRun
                   deriving (Eq, Show)

data HornAppReturnType = HornInt | HornBool

data HornExpr =
  HConstant Id
  | HBool Bool
  | HInt  Int
  | HVar { hVarName   :: Id
         , hVarModule :: Id
         , hVarIndex  :: Int
         , hVarType   :: HornVarType
         , hVarRun    :: HornVarRun
         }
  | HAnd { hAppArgs :: L HornExpr }
  | HOr  { hAppArgs :: L HornExpr }
  | HBinary { hBinaryOp  :: HornBinaryOp
            , hBinaryLhs :: HornExpr
            , hBinaryRhs :: HornExpr
            }
  | HApp { hAppFun  :: Id                -- ^ a unique function name
         , hAppRet  :: HornAppReturnType -- ^ function return type
         , hAppArgs :: L HornExpr        -- ^ function arguments
         }
  | HNot { hNotArg :: HornExpr }
  | KVar { hKVarId   :: Int
         , hKVarSubs :: L (HornExpr, HornExpr)
         }

mkEqual :: (HornExpr, HornExpr) -> HornExpr
mkEqual (e1, e2) = HBinary op e1 e2
  where op = if isBoolean e1 || isBoolean e2 then HIff else HEquals


isBoolean :: HornExpr -> Bool
isBoolean (HBool _) = True
isBoolean HVar{..}  = hVarType == Tag
isBoolean HAnd{..}  = True
isBoolean HOr{..}   = True
isBoolean HNot{..}  = True
isBoolean _         = False

moduleVariables :: Module a -> L HornExpr
moduleVariables m =
  foldl' addVars mempty (variableName . portVariable <$> ports m)
  where
    addVars l v = l <> allHornVars v (IIR.moduleName m)

instance Show HornBinaryOp where
  show HEquals    = "="
  show HNotEquals = "!="
  show HImplies   = "=>"
  show HIff       = "<=>"

instance Show HornExpr where
  show = PP.render . go
    where
      text = PP.text . T.unpack
      goArgs = PP.cat . PP.punctuate (PP.comma PP.<+> PP.empty) . toList . fmap go
      goL = PP.brackets . goArgs
      go = \case
        HConstant c -> text c
        HBool b     -> PP.text $ show b
        HInt n      -> PP.int n
        HVar{..}    ->
          let prefix = case (hVarType, hVarRun) of
                         (Tag, LeftRun)    -> "TL"
                         (Tag, RightRun)   -> "TR"
                         (Value, LeftRun)  -> "VL"
                         (Value, RightRun) -> "VR"
          in PP.hcat $ PP.punctuate (PP.char '.')
             [PP.text prefix , text hVarModule , text hVarName , PP.int hVarIndex]
        HAnd es -> PP.text "&&" PP.<+> goL es
        HOr es -> PP.text "||" PP.<+> goL es
        HBinary{..} -> PP.hsep [go hBinaryLhs, PP.text (show hBinaryOp), go hBinaryRhs]
        HApp{..} -> text hAppFun PP.<> PP.parens (goArgs hAppArgs)
        HNot e -> PP.char '!' PP.<+> go e
        KVar{..} ->
          let args =
                toList $
                (\(v,e) -> PP.brackets $ PP.hsep [ go v , PP.text ":=" , go e]) <$>
                hKVarSubs
          in PP.hcat [ PP.char '$'
                     , PP.text "inv"
                     , PP.int hKVarId
                     , PP.hcat args
                     ]


instance FT.Fixpoint HornType where
       toFix Init          = PP.text "init"
       toFix TagReset      = PP.text "tag-reset"
       toFix SourceReset   = PP.text "source-reset"
       toFix Next          = PP.text "next"
       toFix TagEqual      = PP.text "tag-equal"
       toFix Interference  = PP.text "interference"
       toFix AssertEqCheck = PP.text "assert-eq"
       toFix WellFormed    = PP.text "wellformed"
       toFix InstanceCheck = PP.text "instance-check"
       toFix ModuleSummary = PP.text "module-summary"

instance NFData HornType

-- Variable patterns

pattern HVar0 :: Id -> Id -> HornVarType -> HornVarRun -> HornExpr
pattern HVar0 v m t r =
  HVar { hVarName   = v
       , hVarModule = m
       , hVarIndex  = 0
       , hVarType   = t
       , hVarRun    = r
       }

pattern HVarT0 :: Id -> Id -> HornVarRun -> HornExpr
pattern HVarT0 v m r = HVar0 v m Tag r


pattern HVarVL, HVarVR, HVarTL, HVarTR :: Id -> Id -> Int -> HornExpr
pattern HVarVL v m n = HVar v m n Value LeftRun
pattern HVarVR v m n = HVar v m n Value RightRun
pattern HVarTL v m n = HVar v m n Tag   LeftRun
pattern HVarTR v m n = HVar v m n Tag   RightRun


pattern HVarVL0, HVarVR0, HVarTL0, HVarTR0 :: Id -> Id -> HornExpr
pattern HVarVL0 v m = HVarVL v m 0
pattern HVarVR0 v m = HVarVR v m 0
pattern HVarTL0 v m = HVarTL v m 0
pattern HVarTR0 v m = HVarTR v m 0

allHornVars :: Id -> Id -> L HornExpr
allHornVars v m =
  SQ.empty SQ.|> HVarVL0 v m SQ.|> HVarVR0 v m SQ.|> HVarTL0 v m SQ.|> HVarTR0 v m


toHornVar :: Expr Int -> HornVarType -> HornVarRun -> HornExpr
toHornVar Variable{..} t r =
  HVar { hVarName   = varName
       , hVarModule = varModuleName
       , hVarIndex  = exprData
       , hVarType   = t
       , hVarRun    = r
       }
toHornVar _ _ _ = undefined
