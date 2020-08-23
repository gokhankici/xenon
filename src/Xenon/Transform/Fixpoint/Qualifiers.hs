{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Xenon.Transform.Fixpoint.Qualifiers
  ( defaultQualifiers
  , generateQualifiers
  , generateAutoQualifiers
  ) where

import           Xenon.Language.Annotation
import           Xenon.Language.IR
import           Xenon.Transform.Fixpoint.Common
import           Xenon.Transform.Horn
import           Xenon.Types
import           Xenon.Utils
import           Xenon.ConstantConfig

import           Control.Effect.Reader
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashSet as HS
import qualified Language.Fixpoint.Types as FT


{-|
Creates the following qualifiers:

1. VL_$1   =  VR_$1
2. VLT_$1 <=> VRT_$2
3. VLT_$1 <=> false
4. VRT_$1 <=> false
-}
defaultQualifiers :: L FT.Qualifier
defaultQualifiers =
    mkEq "ValueEq" Value sameValueSuffix
    |:> mkEq "TagEq" Tag sameTagSuffix
    |> mkTagZero 0 LeftRun
    |> mkTagZero 1 RightRun
 where
  sameValueSuffix = True
  sameTagSuffix   = enableQualifierGuess
  mkEq name t sameSuffix =
    makeQualifier2 name t
    (FT.PatPrefix (symbol $ getVarPrefix t LeftRun) 1)
    (FT.PatPrefix (symbol $ getVarPrefix t RightRun) (if sameSuffix then 1 else 2))

  mkTagZero n r = FT.mkQual
    (FT.symbol @String ("TagZero" ++ show n))
    [ FT.QP vSymbol FT.PatNone FT.FInt
    , FT.QP (symbol "x")
            (FT.PatPrefix (symbol $ getVarPrefix Tag r) 1)
            (FT.FTC FT.boolFTyCon)
    ]
    (FT.PIff (FT.eVar @Id "x") FT.PFalse)
    (FT.dummyPos "")


-- | Creates the fixpoint qualifier based on the description given in the
-- annotation file
generateQualifiers :: QFD sig m => Qualifier -> m ()

{-|
For the following annotation:

@
{ "type": "implies", "lhs": "lvar", "rhs": ["rvar1", "rvar2", ...] }
@

the following qualifier is generated:

VLT_lvar => VLT_rvar1 || VLT_rvar2 || ...
-}
generateQualifiers (QImplies lhs rhss) = do
  m <- asks @M moduleName
  let q n = makeQualifierN ("CustomImp_" ++ show n) m LeftRun
            lhs FT.PImp rhss
  q <$> freshQualifierId >>= addQualifier


{-|
For the following annotation:

@
{ "type": "pairs", "variables":  ["v1", "v2", "v3" ...] }
@

the following qualifier is generated for every (vi, vj) pair:

VLT_v1 <=> VLT_v2
-}
generateQualifiers (QPairs vs) =
  for_ varPairs $ \pair ->
    (q pair <$> freshQualifierId) >>=
    addQualifier
 where
  varPairs = twoPairs vs
  vp = getVarPrefix Tag LeftRun
  q (v1, v2) n =
    makeQualifier2 ("Custom2_" ++ show n) Tag
    (FT.PatPrefix (symbol $ vp <> v1) 1)
    (FT.PatPrefix (symbol $ vp <> v2) 1)


{-|
For the following annotation:

@
{ "type": "implies", "lhs": "lvar", "rhs": ["rvar1", "rvar2", ...] }
@

the following qualifiers are generated:

1. VLT_lvar <=> VLT_rvar1 || VLT_rvar2 || ...
2. VRT_lvar <=> VRT_rvar1 || VRT_rvar2 || ...
-}
generateQualifiers (QIff lhs rhss) = do
  m <- asks @M moduleName
  let q n = makeQualifierN ("CustomIff_" ++ show n) m LeftRun
            lhs FT.PIff rhss
  q <$> freshQualifierId >>= addQualifier


{-|
Creates the following qualifiers based on the annotations:

1. Create a qualifier equating the tags of every source pairs
-}
generateAutoQualifiers :: FD sig m => AnnotationFile -> m ()
generateAutoQualifiers af = forM_ sourcePairs $ \(s1, s2) ->
  mkQ (mkVar s1) (mkVar s2) <$> freshQualifierId >>= addQualifier
  where
    annots = toAnnotations topModuleName af
    topModuleName = af ^. afTopModule
    srcs = HS.foldl' (|>) mempty (annots ^. sources)

    sourcePairs = twoPairs srcs
    vp = getVarPrefix Tag LeftRun
    -- sources     = getSourceVar <$> SQ.filter isSource afAnnotations
    mkQ s1 s2 n = makeQualifier2 ("SrcTagEq_" ++ show n) Tag
                  (FT.PatPrefix (symbol s1) 1)
                  (FT.PatPrefix (symbol s2) 1)
    mkVar v     = vp <> v


-- | create a qualifier where the given patterns are compared
makeQualifier2 :: String         -- ^ name of the qualifier
               -> HornVarType    -- ^ type of its operands
               -> FT.QualPattern -- ^ lhs of the operation
               -> FT.QualPattern -- ^ rhs of the operation
               -> FT.Qualifier
makeQualifier2 name t lhs rhs =
  FT.mkQual
  (FT.symbol name)
  [ FT.QP vSymbol FT.PatNone FT.FInt
  , FT.QP (symbol "x") lhs typ
  , FT.QP (symbol "y") rhs typ
  ]
  (FT.eVar @Id "x" `fOp` FT.eVar @Id "y")
  (FT.dummyPos "")

  where
    (typ, fOp) = case t of
      Value -> (FT.intSort,  FT.PAtom FT.Eq)
      Tag   -> (FT.boolSort, FT.PIff)

type FTBinOp = FT.Expr -> FT.Expr -> FT.Expr


{-|
Creates the following qualifier between the boolean values:

lhs @ftBinOp@ (rhs_1 || rhs_2 || rhs_3 || ...)
-}
makeQualifierN :: String        -- ^ name of the qualifier
               -> Id            -- ^ module name
               -> HornVarRun    -- ^ run type
               -> Id            -- ^ lhs of the operation
               -> FTBinOp       -- ^ binary operator
               -> L Id          -- ^ rhs of the operation
               -> FT.Qualifier
makeQualifierN name m r lhs fOp rhss =
  FT.mkQual
  (FT.symbol name)
  ( [ FT.QP vSymbol FT.PatNone FT.FInt
    , FT.QP (symbol "x0") (FT.PatExact (symbol l)) typ
    ] ++
    [ FT.QP (FT.symbol $ "x" ++ show n) (FT.PatExact (symbol v)) typ
    | (n, v) <- numberedRhss
    ]
  )
  (FT.eVar @String "x0"
   `fOp`
   FT.POr [FT.eVar ("x" ++ show n) | (n, _) <- numberedRhss]
  )
  (FT.dummyPos "")
  where
    mkVar v      = mkVarT0 v m r
    l            = mkVar lhs
    rs           = mkVar <$> rhss
    numberedRhss = zip [1..] $ toList rs
    typ          = FT.boolSort
    mkVarT0      = curry3 $ getFixpointName True . uncurry3 HVarT0
