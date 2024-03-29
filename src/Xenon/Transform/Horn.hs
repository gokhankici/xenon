{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Xenon.Transform.Horn where

import           Xenon.Language.IR
import qualified Xenon.Language.IR as IIR
import           Xenon.Types

import           Control.DeepSeq
import           Control.Lens ((|>))
import           Data.Bifunctor
import           Data.Foldable
import           Data.Hashable
import qualified Data.Text as T
import           GHC.Generics
import qualified Language.Fixpoint.Types as FT
import qualified Text.PrettyPrint as PP
import qualified Data.IntMap as IM
import           Control.Effect.Reader

data Horn a =
       Horn { hornHead   :: HornExpr
            , hornBody   :: HornExpr
            , hornType   :: HornType
            , hornStmtId :: Int
            , hornData   :: a
            }
       deriving (Show, Functor)


data HornBinaryOp = HEquals | HNotEquals | HImplies | HIff deriving (Eq, Generic)

data HornType = Init
              | TagSet
              | SourceTagReset
              | Next
              | TagEqual
              | Interference [Int]
              | AssertEqCheck
              | WellFormed
              | InstanceCheck
              | Summary
              deriving (Eq, Show, Generic, Read)

data HornVarType = Tag | Value
                   deriving (Eq, Show, Generic)

data HornVarRun  = LeftRun | RightRun
                   deriving (Eq, Show, Generic)

data HornAppReturnType = HornInt | HornBool deriving (Eq, Show, Generic)

data HornExpr =
  HConstant Id
  | HBool Bool
  | HInt  Int
  | HVar { hVarName   :: Id          -- ^ variable name
         , hVarModule :: Id          -- ^ module name
         , hVarIndex  :: Int         -- ^ index used for temporary variables
         , hVarType   :: HornVarType -- ^ value or tag
         , hVarRun    :: HornVarRun  -- ^ left or right
         , hThreadId  :: Int         -- ^ thread index
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
  | HIte { hIteCond :: HornExpr
         , hIteThen :: HornExpr
         , hIteElse :: HornExpr
         }
  deriving (Eq, Generic)

instance Hashable HornVarType
instance Hashable HornVarRun

instance Hashable HornExpr where
  hashWithSalt n (HConstant v) = hashWithSalt n v
  hashWithSalt n (HBool b)     = hashWithSalt n b
  hashWithSalt _ (HInt n)      = n
  hashWithSalt n HVar{..}      = hashWithSalt n ( hVarName
                                                , hVarModule
                                                , hVarIndex
                                                , hVarType
                                                , hVarRun
                                                , hThreadId
                                                )
  hashWithSalt _ _ = undefined

class MakeKVar m where
  getThreadId :: m Int -> Int

  makeEmptyKVar :: m Int -> HornExpr
  makeEmptyKVar t = KVar (getThreadId t) mempty

  makeKVar :: m Int -> L (HornExpr, HornExpr) -> HornExpr
  makeKVar t = KVar (getThreadId t) . fmap (first $ setThreadId t)

instance MakeKVar AlwaysBlock where
  getThreadId = getData

instance MakeKVar Module where
  getThreadId = getData

setThreadId :: MakeKVar m => m Int -> HornExpr -> HornExpr
setThreadId t = updateThreadId (const $ getThreadId t)

updateVarIndex :: (Int -> Int) -> HornExpr -> HornExpr
updateVarIndex f = updateVarIndex2 (\_v n -> f n)

-- | update the variable index with the given function
updateVarIndex2 :: (Id -> Int -> Int) -> HornExpr -> HornExpr
updateVarIndex2 f = \case
  HVar{..}    -> HVar{ hVarIndex = f hVarName hVarIndex, .. }
  HAnd es     -> HAnd $ go <$> es
  HOr es      -> HOr $ go <$> es
  HBinary{..} -> HBinary{ hBinaryLhs = go hBinaryLhs
                        , hBinaryRhs = go hBinaryRhs
                        , ..
                        }
  HApp{..}    -> HApp{ hAppArgs = go <$> hAppArgs, .. }
  HNot e      -> HNot $ go e
  KVar{..}    -> KVar{ hKVarSubs = second go <$> hKVarSubs, .. }
  HConstant c -> HConstant c
  HInt n      -> HInt n
  HBool b     -> HBool b
  HIte{..}    -> HIte { hIteCond = go hIteCond
                      , hIteThen = go hIteThen
                      , hIteElse = go hIteElse
                      }
  where go = updateVarIndex2 f

-- | update the thread index with the given function
updateThreadId :: (Int -> Int) -> HornExpr -> HornExpr
updateThreadId f = \case
  HVar{..}    -> HVar{ hThreadId = f hThreadId, .. }
  HAnd es     -> HAnd $ go <$> es
  HOr es      -> HOr $ go <$> es
  HBinary{..} -> HBinary{ hBinaryLhs = go hBinaryLhs
                        , hBinaryRhs = go hBinaryRhs
                        , ..
                        }
  HApp{..}    -> HApp{ hAppArgs = go <$> hAppArgs, .. }
  HNot e      -> HNot $ go e
  KVar{..}    -> KVar{ hKVarSubs = second go <$> hKVarSubs, .. }
  HConstant c -> HConstant c
  HInt n      -> HInt n
  HBool b     -> HBool b
  HIte{..}    -> HIte { hIteCond = go hIteCond
                      , hIteThen = go hIteThen
                      , hIteElse = go hIteElse
                      }
  where go = updateThreadId f

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
        HIte{..}    -> PP.parens $
                       go hIteCond PP.<+> PP.text "?" PP.<+>
                       go hIteThen PP.<+> PP.text ":" PP.<+>
                       go hIteElse
        HVar{..}    ->
          let prefix = case (hVarType, hVarRun) of
                         (Tag, LeftRun)    -> "TL"
                         (Tag, RightRun)   -> "TR"
                         (Value, LeftRun)  -> "VL"
                         (Value, RightRun) -> "VR"
          in PP.hcat $ PP.punctuate (PP.char '.')
             [ PP.text prefix
             , text hVarModule
             , PP.text "T" PP.<> PP.int hThreadId
             , text hVarName
             , PP.int hVarIndex
             ]
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
       toFix Init           = PP.text "init"
       toFix TagSet         = PP.text "tag-set"
       toFix SourceTagReset = PP.text "source-tag-reset"
       toFix Next           = PP.text "next"
       toFix TagEqual       = PP.text "tag-equal"
       toFix AssertEqCheck  = PP.text "assert-eq"
       toFix WellFormed     = PP.text "wellformed"
       toFix InstanceCheck  = PP.text "instance-check"
       toFix Summary        = PP.text "module-summary"
       toFix (Interference l) =
         let arr = PP.brackets . PP.hsep . PP.punctuate PP.comma . fmap PP.int
         in PP.text "interference" PP.<+> arr l

instance NFData HornType

-- Variable patterns

pattern HVar0 :: Id -> Id -> HornVarType -> HornVarRun -> HornExpr
pattern HVar0 v m t r =
  HVar { hVarName   = v
       , hVarModule = m
       , hVarIndex  = 0
       , hVarType   = t
       , hVarRun    = r
       , hThreadId  = 0
       }

pattern HVarT0 :: Id -> Id -> HornVarRun -> HornExpr
pattern HVarT0 v m r = HVar0 v m Tag r


pattern HVarVL, HVarVR, HVarTL, HVarTR :: Id -> Id -> Int -> HornExpr
pattern HVarVL v m n = HVar v m n Value LeftRun  0
pattern HVarVR v m n = HVar v m n Value RightRun 0
pattern HVarTL v m n = HVar v m n Tag   LeftRun  0
pattern HVarTR v m n = HVar v m n Tag   RightRun 0


pattern HVarVL0, HVarVR0, HVarTL0, HVarTR0 :: Id -> Id -> HornExpr
pattern HVarVL0 v m = HVarVL v m 0
pattern HVarVR0 v m = HVarVR v m 0
pattern HVarTL0 v m = HVarTL v m 0
pattern HVarTR0 v m = HVarTR v m 0

allHornVars :: Id -> Id -> L HornExpr
allHornVars v m = uncurry (HVar0 v m) <$> allTagRuns

allTagRuns :: L (HornVarType, HornVarRun)
allTagRuns =
  mempty |>
  (Value, LeftRun) |>
  (Value, RightRun) |>
  (Tag,   LeftRun) |>
  (Tag,   RightRun)


toHornVar :: Expr Int -> HornVarType -> HornVarRun -> HornExpr
toHornVar Variable{..} t r =
  HVar { hVarName   = varName
       , hVarModule = varModuleName
       , hVarIndex  = exprData
       , hVarType   = t
       , hVarRun    = r
       , hThreadId  = 0
       }
toHornVar _ _ _ = undefined

isHornVariable :: HornExpr -> Bool
isHornVariable HVar{} = True
isHornVariable _      = False

mkHornVar :: Expr Int -> HornVarType -> HornVarRun -> HornExpr
mkHornVar e@Variable{..} t r =
  HVar { hVarName   = varName
       , hVarModule = varModuleName
       , hVarIndex  = getData e
       , hVarType   = t
       , hVarRun    = r
       , hThreadId  = 0
       }
mkHornVar _ _ _ =
  error "mkHornVar must be called with an IR variable"

newtype HornVariableMap = HornVariableMap { getHornVariablesMap :: IM.IntMap Ids }

askHornVariablesMap :: (Has (Reader HornVariableMap) sig m, MakeKVar t) => t Int -> m Ids
askHornVariablesMap t = (IM.! getThreadId t) <$> asks getHornVariablesMap