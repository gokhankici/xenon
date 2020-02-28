{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Iodine.Transform.HornQuery
  ( constructQuery
  )
where

import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Horn
import           Iodine.Types
import           Iodine.Utils

import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntMap as IM
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import qualified Language.Fixpoint.Horn.Info as FHI
import qualified Language.Fixpoint.Horn.Types as FHT
import qualified Language.Fixpoint.Types as FT
import           Polysemy
import qualified Polysemy.Error as PE
import           Polysemy.Reader
import           Polysemy.State
import           Polysemy.Trace
import           Text.Printf
-- import qualified Data.Vector as V

-- import           Control.DeepSeq
-- import           GHC.Generics hiding ( moduleName, to )
-- import qualified Text.PrettyPrint.HughesPJ as PP


-- -----------------------------------------------------------------------------
-- type definitions
-- -----------------------------------------------------------------------------

type Horns = L (Horn ())
type ModuleMap = HM.HashMap Id (Module Int)

type G r = Members '[ Trace
                    , Reader AnnotationFile
                    , PE.Error IodineException
                    , Reader ModuleMap
                    ] r
type FD r  = (G r, Member (State St) r)
type FDM r = (FD r, Member (Reader (Module Int)) r)


-- -----------------------------------------------------------------------------
-- solver state
-- -----------------------------------------------------------------------------

data St = St { _constraints :: L (FHT.Cstr ())
             , _qualifiers  :: L FT.Qualifier
             , _constants   :: HM.HashMap FT.Symbol FT.Sort
             , _kvars       :: L (FHT.Var ())

             , _invVarMap        :: IM.IntMap (HM.HashMap Id Int)
             , _qualifierCounter :: Int
             }

makeLenses ''St

initialSt :: St
initialSt = St mempty defaultQualifiers mempty mempty mempty 0

st2FInfo :: St -> FT.FInfo ()
st2FInfo st = FHI.hornFInfo query
  where
    vs = toList $ st ^. kvars
    qs = toList $ st ^. qualifiers
    cs = toList $ st ^. constraints
    query = FHT.Query qs vs (FHT.CAnd cs) (st ^. constants) mempty


-- -----------------------------------------------------------------------------
-- generate a query for the liquid-fixpoint solver
-- -----------------------------------------------------------------------------

-- | Given the verification conditions, generate the query to be sent to the
-- fixpoint solver
constructQuery :: G r => Horns -> Sem r (FT.FInfo ())
constructQuery horns = fmap st2FInfo . execState initialSt $ do
  asks @ModuleMap HM.elems >>= traverse_ handleModule
  ask >>= generateAutoQualifiers
  for_ horns handleHorn


handleModule :: FD r => Module Int -> Sem r ()
handleModule m = do
  setInvVarMap m
  addSummaryQualifiers m
  (getQualifiers (moduleName m) >>= traverse_ generateQualifiers) & runReader m


-- | 1. Add the kvars of the threads of this module.
--   2. Update the kvar variable map for the variables of the threads.
setInvVarMap :: FD r => Module Int -> Sem r ()
setInvVarMap m@Module{..} = for_ (IM.keys varMap) $ \n -> do
  let params = toList $ getKVarParams n -- parameters of the kvar
  modify $ kvars %~ (|> mkVar n params)
  modify $ invVarMap %~ IM.insert n (list2map params)

  where
    -- instead of using all the variables that occur in this thread, only keep
    -- the variables that are ports or appear in at least one other thread
    getKVarParams :: Int -> Ids
    getKVarParams n =
      let nParams = varMap IM.! n
      in IM.foldlWithKey'
         (\acc n2 n2Params ->
            if   n == n2
            then acc
            else acc `HS.union` (nParams `HS.intersection` n2Params))
         mempty
         varMap

    -- all variables of the threads
    varMap :: IM.IntMap Ids
    varMap =
      IM.fromList $
      (getData m, getVariables m) :
      ((\t -> (getData t, getVariables t)) <$> threads)

    -- threads of this module
    threads :: [Thread Int]
    threads = toList $ (AB <$> alwaysBlocks) <> (MI <$> moduleInstances)

    -- make a kvar
    mkVar :: Int -> [Id] -> FHT.Var ()
    mkVar kvarId vars = FHT.HVar (kvarSymbol kvarId) (mkKVarSorts vars) ()

    -- sorts of a kvar with variables
    mkKVarSorts :: [Id] -> [(FT.Symbol, FT.Sort)]
    mkKVarSorts vars =
      foldr'
      (\v acc ->
         let go  = getFixpointSymbol True
             vl  = go $ HVarVL0 v moduleName
             vr  = go $ HVarVR0 v moduleName
             vlt = go $ HVarTL0 v moduleName
             vrt = go $ HVarTR0 v moduleName
         in (vl, is):(vr, is):(vlt, bs):(vrt, bs):acc
      ) [] vars

    is, bs :: FT.Sort
    is = FT.intSort
    bs = FT.boolSort

    list2map :: [Id] -> HM.HashMap Id Int
    list2map ss = HM.fromList (zip ss [0..])


-- -----------------------------------------------------------------------------
-- Horn -> Cstr
-- -----------------------------------------------------------------------------

handleHorn :: FD r => Horn () -> Sem r (FHT.Cstr ())
handleHorn h@Horn{..} = do
  headPred <- convertExprP hornHead
  bodyPred <- convertExprP hornBody
  bindSet <- hornVariables h
  return $ mkForAll (toList bindSet) bodyPred (FHT.Head headPred ())

mkForAll :: [(Id, Id, Int)] -> FHT.Pred -> FHT.Cstr () -> FHT.Cstr ()
mkForAll ((v,m,n):rest) pBody cHead =
  FHT.All b1 $ FHT.All b2 $ FHT.All b3 $ FHT.All b4' $ c

  where
    c = case rest of
          [] -> cHead
          _  -> mkForAll rest pBody cHead

    b4' = case rest of
            [] -> b4 { FHT.bPred = pBody }
            _  -> b4

    b1 = mkBind Value LeftRun
    b2 = mkBind Value RightRun
    b3 = mkBind Tag   LeftRun
    b4 = mkBind Tag   RightRun

    mkBind t r =
      FHT.Bind
      (getFixpointSymbol False $ HVar v m n t r)
      (toS t)
      (FHT.Reft $ FT.prop True)

    toS = \case
      Value -> FT.intSort
      Tag   -> FT.boolSort

mkForAll [] _ _ = error "mkForAll called with empty variable list"


hornVariables :: FD r => Horn () -> Sem r (HS.HashSet (Id, Id, Int))
hornVariables Horn{..} = mappend <$> go hornBody <*> go hornHead
  where
    go :: FD r => HornExpr -> Sem r (HS.HashSet (Id, Id, Int))
    go = \case
      HConstant _  -> return mempty
      HBool _      -> return mempty
      HInt _       -> return mempty
      HVar{..}     -> return $ HS.singleton (hVarName, hVarModule, hVarIndex)
      HAnd es      -> mfoldM go es
      HOr es       -> mfoldM go es
      HBinary{..}  -> mappend <$> go hBinaryLhs <*> go hBinaryRhs
      HApp{..}     -> mfoldM go hAppArgs
      HNot e       -> go e
      k@KVar{}     -> getKVarArgs k >>= mfoldM go


getKVarArgs :: FD r => HornExpr -> Sem r [HornExpr]
getKVarArgs KVar{..} = undefined
getKVarArgs _        = PE.throw $ IE Query "getKVarArgs must be called with a kvar"

-- -----------------------------------------------------------------------------
-- HornExpr -> FHT.Pred   and   HornExpr -> FT.Expr
-- -----------------------------------------------------------------------------

convertExprP :: FD r => HornExpr -> Sem r FHT.Pred
convertExpr  :: FD r => HornExpr -> Sem r FT.Expr

convertExprP (HAnd es) =
  case es of
    SQ.Empty -> FHT.Reft <$> convertExpr (HBool True)
    _        -> FHT.PAnd . toList <$> traverse convertExprP es

convertExprP KVar{..} =
  FHT.Var (kvarSymbol hKVarId)
  . (fmap $ getFixpointSymbol False)
  <$> getKVarArgs KVar{..}

convertExprP e = FHT.Reft <$> convertExpr e


-- | create a global constant in the environment
convertExpr (HConstant c) = do
  globals <- gets (^. constants)
  unless (HM.member sym globals)
    $ modify (constants %~ HM.insert sym FT.intSort)
  return $ FT.ECon $ FT.L constName FT.intSort
 where
  constName = "const_" <> c
  sym       = symbol constName

-- | return the corresponding binding for True or False
convertExpr (HBool b) = return $ FT.prop b

convertExpr (HInt i) = return . FT.ECon . FT.I . toInteger $ i

-- | return the fixpoint name of the variable after updating the current bind
-- environment
convertExpr var@HVar {..} =
  return $ FT.eVar (getFixpointName False var)

convertExpr (HAnd es) =
  case es of
    SQ.Empty -> convertExpr (HBool True)
    _        -> FT.PAnd . toList <$> traverse convertExpr es

convertExpr (HOr es) =
  case es of
    SQ.Empty -> convertExpr (HBool False)
    _        -> FT.POr . toList <$> traverse convertExpr es

convertExpr HBinary {..} =
  case hBinaryOp of
    HEquals    -> FT.EEq         <$> convertExpr hBinaryLhs <*> convertExpr hBinaryRhs
    HNotEquals -> FT.PAtom FT.Ne <$> convertExpr hBinaryLhs <*> convertExpr hBinaryRhs
    HImplies   -> FT.PImp        <$> convertExpr hBinaryLhs <*> convertExpr hBinaryRhs
    HIff       -> FT.PIff        <$> convertExpr hBinaryLhs <*> convertExpr hBinaryRhs

convertExpr HNot {..} = FT.PNot <$> convertExpr hNotArg

-- | create a new uninterpreted function if the function application does not
-- have a name for the function
convertExpr HApp {..} = do
  let fsym = symbol hAppFun
  modify (constants %~ HM.insert fsym sort)
  FT.mkEApp (FT.dummyLoc fsym) . toList <$> traverse convertExpr hAppArgs

 where
  arity = SQ.length hAppArgs
  ret   = toFSort hAppRet
  sort  = if arity > 0
          then FT.mkFFunc 0 $ (replicate arity FT.intSort) ++ [ret]
          else ret
  toFSort = \case
    HornInt  -> FT.intSort
    HornBool -> FT.boolSort

convertExpr KVar {..} =
  PE.throw $ IE Query "convertExpr KVar must be unreachable"


-- -----------------------------------------------------------------------------
-- generate qualifiers
-- -----------------------------------------------------------------------------

{-|
Creates the following qualifiers:

1. VL_$1   =  VR_$1
2. VLT_$1 <=> VRT_$2
3. VLT_$1 <=> false
4. VRT_$1 <=> false
-}
defaultQualifiers :: L FT.Qualifier
defaultQualifiers =
    mkEq "ValueEq" Value True
    |:> mkEq "TagEq" Tag False
    |> mkTagZero 0 LeftRun
    |> mkTagZero 1 RightRun
 where
  mkEq name t sameSuffix =
    makeQualifier2 name t
    (FT.PatPrefix (symbol $ getVarPrefix t LeftRun) 1)
    (FT.PatPrefix (symbol $ getVarPrefix t RightRun) (if sameSuffix then 1 else 2))

  mkTagZero n r = FT.mkQual
    (FT.symbol @String (printf "TagZero%d" (n :: Int)))
    [ FT.QP vSymbol FT.PatNone FT.FInt
    , FT.QP (symbol "x")
            (FT.PatPrefix (symbol $ getVarPrefix Tag r) 1)
            (FT.FTC FT.boolFTyCon)
    ]
    (FT.PIff (FT.eVar @Id "x") FT.PFalse)
    (FT.dummyPos "")


-- | Creates the fixpoint qualifier based on the description given in the
-- annotation file
generateQualifiers :: FDM r => Qualifier -> Sem r ()

{-|
For the following annotation:

@
{ "type": "implies", "lhs": "lvar", "rhs": ["rvar1", "rvar2", ...] }
@

the following qualifier is generated:

VLT_lvar => VLT_rvar1 || VLT_rvar2 || ...
-}
generateQualifiers (QImplies lhs rhss) = do
  m <- asks moduleName
  let q n = makeQualifierN ("CustomImp_" ++ show n) m LeftRun
            lhs (FT.PImp) rhss
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
  (varPairs <$> asks moduleName) >>=
  traverse_ (\pair ->
               (q pair <$> freshQualifierId) >>=
               addQualifier)
 where
  vars m       = (`HVarTL0` m) <$> vs
  varPairs m   = twoPairs $ getFixpointSymbol True <$> vars m
  q (s1, s2) n =
    makeQualifier2 ("Custom2_" ++ show n) Tag
    (FT.PatExact s1)
    (FT.PatExact s2)


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
  m <- asks moduleName
  let q n = makeQualifierN ("CustomIff_" ++ show n) m LeftRun
            lhs (FT.PIff) rhss
  q <$> freshQualifierId >>= addQualifier


{-|
Creates the following qualifiers based on the annotations:

1. Create a qualifier equating the tags of every source pairs
-}
generateAutoQualifiers :: FD r => AnnotationFile -> Sem r ()
generateAutoQualifiers af = forM_ sourcePairs $ \(s1, s2) ->
  mkQ (mkVar s1) (mkVar s2) <$> freshQualifierId >>= addQualifier
  where
    annots = toAnnotations topModuleName af
    topModuleName = af ^. afTopModule
    srcs = HS.foldl' (|>) mempty (annots ^. sources)

    sourcePairs = twoPairs srcs
    -- sources     = getSourceVar <$> SQ.filter isSource afAnnotations
    mkQ s1 s2 n = makeQualifier2 ("SrcTagEq_" ++ show n) Tag
                  (FT.PatExact s1)
                  (FT.PatExact s2)
    mkVar v     = getFixpointSymbol True $ HVarTL0 v topModuleName


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
    , FT.QP (symbol "x0") (FT.PatExact l) typ
    ] ++
    [ FT.QP (FT.symbol $ "x" ++ show n) (FT.PatExact v) typ
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
    mkVarT0      = curry3 $ getFixpointSymbol True . uncurry3 HVarT0


addSummaryQualifiers :: FD r => Module Int -> Sem r ()
addSummaryQualifiers m@Module{..} = do
  mClk <- getClock moduleName
  let noClk a    = Just a /= mClk
  let inputs     = SQ.filter noClk (moduleInputs m)
  let nonInput a = Just a /= mClk && not (elem a inputs)
  let vars       = SQ.filter nonInput (variableName <$> variables)
  let foos = do ls <- toList $ powerset inputs
                r  <- toList vars
                return (ls, r)
  for_ (zip foos [0..]) $ \((ls, r), n) ->
    addQualifier $ mkSummaryQualifier n moduleName ls r


mkSummaryQualifier :: Int -> Id -> L Id -> Id -> FT.Qualifier
mkSummaryQualifier n moduleName ls r =
  FT.mkQual
  (FT.symbol $ "summaryQualifier_" ++ T.unpack moduleName ++ "_" ++ show n)
  ( [ FT.QP vSymbol FT.PatNone FT.FInt
    , FT.QP (symbol "rl") (FT.PatExact (symbol $ mkVar r LeftRun)) typ
    , FT.QP (symbol "rr") (FT.PatExact (symbol $ mkVar r RightRun)) typ
    ] ++
    concat [ [ FT.QP (FT.symbol $ "l" ++ show n2)     (FT.PatExact (symbol $ mkVar l LeftRun)) typ
             , FT.QP (FT.symbol $ "l" ++ show (n2+1)) (FT.PatExact (symbol $ mkVar l RightRun)) typ
             ]
           | (l, n2) <- zip (toList ls) [0,2..]
           ]
  )
  ( FT.PAnd [ FT.eVar ("l" ++ show n2) `FT.PIff` FT.eVar ("l" ++ show (n2+1))
            | (_, n2) <- zip (toList ls) [0,2..]
            ]
    `FT.PImp`
    (FT.eVar @String "rl" `FT.PIff` FT.eVar @String "rr")
  )
  (FT.dummyPos "")
  where
    mkVar v rn =
      getFixpointName True $
      HVar { hVarName   = v
           , hVarModule = moduleName
           , hVarIndex  = 0
           , hVarType   = Tag
           , hVarRun    = rn
           }
    typ = FT.boolSort


-- | non empty powerset of the given sequence
powerset :: L a -> L (L a)
powerset SQ.Empty            = error "powerset should be called with a non-empty list"
powerset (a SQ.:<| SQ.Empty) = SQ.singleton $ SQ.singleton a
powerset (a SQ.:<| as)       = let ps = powerset as
                               in ((a SQ.:<|) <$> (SQ.singleton mempty <> ps)) <> ps


-- -- -----------------------------------------------------------------------------
-- -- helper functions
-- -- -----------------------------------------------------------------------------

-- | get the bind name used for the variable in the query if isParam
getFixpointName :: Bool       -- ^ If true, the hVarIndex will be ignored
                -> HornExpr   -- ^ Only variables are accepted
                -> Id         -- ^ fixpoint variable name
getFixpointName isParam HVar{..} = varno <> prefix <> name
  where
    varno =
      if isParam then "" else "N" <> T.pack (show hVarIndex) <> "_"
    prefix = getVarPrefix hVarType hVarRun
    name   = "M_" <> hVarModule <> "_V_" <> hVarName
getFixpointName _ _ = error "must be called with a variable"


-- | same as 'getFixpointName', but returns a symbol
getFixpointSymbol :: Bool -> HornExpr -> FT.Symbol
getFixpointSymbol b e = symbol $ getFixpointName b e


getVarPrefix :: HornVarType -> HornVarRun -> Id
getVarPrefix hVarType hVarRun =
  case (hVarType, hVarRun) of
    (Value, LeftRun ) -> "VL_"
    (Value, RightRun) -> "VR_"
    (Tag  , LeftRun ) -> "TL_"
    (Tag  , RightRun) -> "TR_"


-- | update the state with the given fixpoint qualifier
addQualifier :: Member (State St) r => FT.Qualifier -> Sem r ()
addQualifier q = modify (& qualifiers %~ (|> q))


-- | return the current qualifier id and increment it later
freshQualifierId :: Member (State St) r => Sem r Int
freshQualifierId =
  gets (^. qualifierCounter) <* modify (& qualifierCounter +~ 1)


-- | return combinations of the elements
twoPairs :: L a -> L (a, a)
twoPairs SQ.Empty      = mempty
twoPairs (a SQ.:<| as) = ((a, ) <$> as) <> twoPairs as


-- -- | make a KVar for the given invariant id
kvarSymbol :: Int -> FT.Symbol
kvarSymbol n = FT.symbol $ "$k" <> show n


-- | variable used in refinements
vSymbol :: FT.Symbol
vSymbol = symbol "v"


symbol :: Id -> FT.Symbol
symbol = FT.symbol


_lookupInvIndex :: FD r => Module Int -> HornExpr -> Sem r (Maybe Int)
_lookupInvIndex m HVar{..} =
  fmap toId . HM.lookup hVarName <$> gets ((IM.! getData m) . (^. invVarMap))
  where
    toId n = case (hVarType, hVarRun) of
               (Value, LeftRun)  -> 4 * n
               (Value, RightRun) -> 4 * n + 1
               (Tag,   LeftRun)  -> 4 * n + 2
               (Tag,   RightRun) -> 4 * n + 3
_lookupInvIndex m e =
  PE.throw . IE Query $
  printf "lookupInvIndex called with %s and %s" (show m) (show e)
