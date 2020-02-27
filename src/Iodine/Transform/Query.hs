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

module Iodine.Transform.Query
  ( constructQuery
  , FInfo
  )
where

import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Horn
import           Iodine.Types
import           Iodine.Utils

import           Control.DeepSeq
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           GHC.Generics hiding ( moduleName, to )
import qualified Language.Fixpoint.Types as FT
import           Polysemy
import           Polysemy.Reader
import           Polysemy.Trace
import           Polysemy.State
import qualified Polysemy.Error as PE
import qualified Text.PrettyPrint.HughesPJ as PP
import           Text.Printf

-- -----------------------------------------------------------------------------
-- type definitions
-- -----------------------------------------------------------------------------

type FInfo = FT.FInfo HornClauseId
type Horns = L (Horn ())
type ModuleMap = HM.HashMap Id (Module Int)

type G r   = Members '[ Trace
                      , Reader AnnotationFile
                      , PE.Error IodineException
                      , Reader ModuleMap
                      ] r

type FD r  = ( G r
             , Member (State St) r
             )

type FDC r = ( FD r
             , Member (State FT.IBindEnv) r
             )

type QFD r = Members '[ Trace
                      , PE.Error IodineException
                      , Reader (Module Int)
                      , State St
                      ] r
-- -----------------------------------------------------------------------------
-- solver state
-- -----------------------------------------------------------------------------

data HornClauseId = HornClauseId { hcStmtId :: Int, hcType :: HornType }
                  deriving (Show, Generic)

data St = St { _hornConstraints           :: HM.HashMap Integer (FT.SubC HornClauseId)
             , _wellFormednessConstraints :: HM.HashMap FT.KVar (FT.WfC HornClauseId)
             , _bindEnvironment           :: FT.BindEnv
             , _globalConstantLiterals    :: FT.SEnv FT.Sort
             , _qualifiers                :: SQ.Seq FT.Qualifier

             , _constraintCounter         :: Integer
             , _qualifierCounter          :: Int
             , _invBindMap                :: HM.HashMap Id FT.BindId
             }

makeLenses ''St


-- -----------------------------------------------------------------------------
-- generate a query for the liquid-fixpoint solver
-- -----------------------------------------------------------------------------

-- | Given the verification conditions, generate the query to be sent to the
-- fixpoint solver
constructQuery :: G r => L (Module Int) -> Horns -> Sem r FInfo
constructQuery modules horns = evalState initialState $ do
  setConstants
  traverse_ generateConstraint horns
  traverse_ generateWFConstraints modules
  for_ modules $ \m@Module{..} ->
    (getQualifiers moduleName >>= traverse_ generateQualifiers) & runReader m
  ask >>= generateAutoQualifiers
  for_ modules addSummaryQualifiers
  toFInfo


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
      getFixpointName $
      HVar { hVarName   = v
           , hVarModule = moduleName
           , hVarIndex  = 0
           , hVarType   = Tag
           , hVarRun    = rn
           }
    typ = FT.boolSort

-- non empty powerset of the given sequence
powerset :: L a -> L (L a)
powerset SQ.Empty            = SQ.Empty
powerset (a SQ.:<| SQ.Empty) = SQ.singleton $ SQ.singleton a
powerset (a SQ.:<| as)       = let ps = powerset as
                               in ps <> ((a SQ.:<|) <$> ps)

-- -----------------------------------------------------------------------------
-- generate constraints
-- -----------------------------------------------------------------------------

-- | Create the fixpoint version of the horn clause
generateConstraint :: FD r => Horn () -> Sem r ()
generateConstraint Horn {..} = do
  (env, (bodyExpr, headExpr)) <-
    (,) <$> convertExpr hornBody <*> convertExpr hornHead
    & runState FT.emptyIBindEnv
  n <- freshConstraintId
  let body = mkInt bodyExpr
      hd   = mkInt headExpr
      md   = HornClauseId hornStmtId hornType
      hc   = FT.mkSubC env body hd (Just n) [] md
  modify ((hornConstraints . at n) ?~ hc)


-- | Create a well formedness constraint for every statement of the module
generateWFConstraints :: FD r => Module Int -> Sem r ()
generateWFConstraints m@Module{..} = do
  traverse_ (generateWFConstraint moduleName . abStmt) alwaysBlocks
  traverse_ (generateWFConstraintMI moduleName) moduleInstances
  generateWFConstraintM m



-- | Create a well formedness constraint for the given statement
generateWFConstraint :: FD r
                     => Id      -- ^ module name
                     -> Stmt Int
                     -> Sem r ()
generateWFConstraint m stmt = do
  -- piggy back on the ienv generation of convertExpr to get the indices
  (ienv, _) <-
    traverse_ convertExpr hvars
    & runState mempty
  case FT.wfC ienv (mkInt e) md of
    [wf] -> modify ((wellFormednessConstraints . at kvar) ?~ wf)
    wfcs -> throw $ "did not get only 1 wfc: " ++ show wfcs
 where
  vars   = getVariables stmt
  hvars  =
    -- include all the type & run pairs for the index 0 of the variable
    mfold (\v -> SQ.empty |>
                 HVarVL0 v m |> HVarVR0 v m |>
                 HVarTL0 v m |> HVarTR0 v m) vars
  stmtId = stmtData stmt
  kvar   = mkKVar stmtId
  e      = FT.PKVar kvar mempty
  md     = HornClauseId stmtId WellFormed

-- | Create a well formedness constraint for the given module instance
generateWFConstraintMI :: FD r
                       => Id    -- ^ module name
                       -> ModuleInstance Int
                       -> Sem r ()
generateWFConstraintMI currentModuleName mi@ModuleInstance{..} = do
  m <- asks @ModuleMap (\m -> case HM.lookup currentModuleName m of
                                Nothing -> undefined
                                Just x  -> x)
  (ienv, _) <- runState mempty $ do
    traverse_ convertExpr (moduleVariables m)
    traverse_ convertExpr $ do
      p <- HM.elems moduleInstancePorts
      t <- [Tag, Value]
      r <- [LeftRun, RightRun]
      return $ toHornVar p t r

  case FT.wfC ienv (mkInt e) md of
    [wf] -> modify ((wellFormednessConstraints . at kvar) ?~ wf)
    wfcs -> throw $ "did not get only 1 wfc: " ++ show wfcs
  where
    n  = getData mi
    kvar = mkKVar n
    e  = FT.PKVar kvar mempty
    md = HornClauseId n InstanceCheck

generateWFConstraintM :: FD r => Module Int -> Sem r ()
generateWFConstraintM m@Module{..} = do
  (ienv, _) <-
    traverse_ convertExpr (moduleVariables m)
    & runState mempty
  case FT.wfC ienv (mkInt e) md of
    [wf] -> modify ((wellFormednessConstraints . at kvar) ?~ wf)
    wfcs -> throw $ "did not get only 1 wfc: " ++ show wfcs
  where
    n  = moduleData
    kvar = mkKVar n
    e  = FT.PKVar kvar mempty
    md = HornClauseId n ModuleSummary

-- -----------------------------------------------------------------------------
-- HornExpr -> FT.Expr
-- -----------------------------------------------------------------------------

convertExpr :: FDC r => HornExpr -> Sem r FT.Expr

-- | create a global constant in the environment
convertExpr (HConstant c) = do
  globals <- gets (^. globalConstantLiterals)
  unless (FT.memberSEnv sym globals)
    $ modify (globalConstantLiterals %~ FT.insertSEnv sym FT.intSort)
  return $ FT.ECon $ FT.L constName FT.intSort
 where
  constName = "const_" <> c
  sym       = symbol constName

-- | return the corresponding binding for True or False
convertExpr (HBool b) = do
  be <- gets (^. invBindMap)
  let n = be HM.! name
  modify (FT.insertsIBindEnv [n])
  return $ FT.eVar name
  where name = if b then "tru" else "fals"

convertExpr (HInt i) = return . FT.ECon . FT.I . toInteger $ i
--   be <- gets (^. invBindMap)
--   n  <- case HM.lookup name be of
--     Just n -> return n
--     Nothing ->
--       let sr = mkInt (FT.EEq (FT.eVar vSymbol) (FT.ECon $ FT.I $ toInteger i))
--       in  addBinding name sr
--   modify (FT.insertsIBindEnv [n])
--   return $ FT.eVar name
--   where name = "number_" <> T.pack (show i)

-- | return the fixpoint name of the variable after updating the current bind
-- environment
convertExpr var@HVar {..} = do
  n <- getVariableId var
  modify (FT.insertsIBindEnv [n])
  return $ FT.eVar (getFixpointName var)

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
  modify (globalConstantLiterals %~ FT.insertSEnv fsym sort)
  FT.mkEApp (FT.dummyLoc fsym) . toList <$> traverse convertExpr hAppArgs
 where
  arity = SQ.length hAppArgs
  ret   = toFSort hAppRet
  sort  = if arity > 0
          then FT.mkFFunc 0 $ (replicate arity FT.intSort) ++ [ret]
          else ret

convertExpr KVar {..} =
  FT.PKVar (mkKVar hKVarId) . FT.mkSubst . toList <$>
  traverse
  (\(lhs, rhs) -> do
      lhs' <- convertExpr lhs
      sym  <-
        case lhs' of
          FT.EVar v -> return v
          _ -> throw $
               "expecting lhs of kvar substitution to be a symbol: " ++ show lhs
      rhs' <- convertExpr rhs
      return (sym, rhs')
  )
  hKVarSubs


-- | return the id of the variable. if the variable does not exist, add it to
-- the environment first.
getVariableId :: FD r => HornExpr -> Sem r FT.BindId
getVariableId v = do
  mid <- HM.lookup name <$> gets (^. invBindMap)
  case mid of
    Just n  -> return n
    Nothing -> addBinding name sr
 where
  name = getFixpointName v
  sr   = case hVarType v of
    Value -> mkInt FT.PTrue
    Tag   -> mkBool FT.PTrue

-- | add the variable name and its sort to the current bind environment
addBinding :: FD r => Id -> FT.SortedReft -> Sem r FT.BindId
addBinding name sr = do
  be <- gets (^. bindEnvironment)
  let (n, be') = FT.insertBindEnv (symbol name) sr be
  modify (bindEnvironment .~ be')
  modify (invBindMap . at name ?~ n)
  return n

toFSort :: HornAppReturnType -> FT.Sort
toFSort HornInt  = FT.intSort
toFSort HornBool = FT.boolSort

-- -----------------------------------------------------------------------------
-- generate qualifiers
-- -----------------------------------------------------------------------------

-- | Creates the fixpoint qualifier based on the description given in the
-- annotation file
generateQualifiers :: QFD r => Qualifier -> Sem r ()

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
  varPairs m   = twoPairs $ getFixpointName <$> vars m
  q (x1, x2) n =
    makeQualifier2 ("Custom2_" ++ show n) Tag
    (FT.PatExact (symbol x1))
    (FT.PatExact (symbol x2))


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
                  (FT.PatExact (symbol s1))
                  (FT.PatExact (symbol s2))
    mkVar v     = getFixpointName $ HVarTL0 v topModuleName


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

-- | return the name of the variable in Tag type with 0 index
mkVarT0 :: Id                 -- ^ variable name
        -> Id                 -- ^ module name
        -> HornVarRun         -- ^ run type
        -> Id
mkVarT0 = curry3 $ getFixpointName . uncurry3 HVarT0

-- -----------------------------------------------------------------------------
-- helper functions
-- -----------------------------------------------------------------------------

-- | We create a binding for true and false values, and use them in the horn
-- clauses instead of the boolean type directly.
setConstants :: FD r => Sem r ()
setConstants = forM_ constants $ uncurry addBinding
 where
  b val = mkBool (FT.PIff (FT.eVar $ vSymbol) val)
  constants = [("tru", b FT.PTrue), ("fals", b FT.PFalse)]


-- | read the current state and create the query for the fixpoint solver
toFInfo :: FD r => Sem r FInfo
toFInfo =
  FT.fi
    <$> (toList <$> gets (^. hornConstraints))
    <*> (toList <$> gets (^. wellFormednessConstraints))
    <*> gets (^. bindEnvironment)
    <*> gets (^. globalConstantLiterals)
    <*> -- distinct constant symbols
        return mempty
    <*> -- set of kvars not to eliminate
        return mempty
    <*> (toList <$> gets (^. qualifiers))
    <*> -- metadata about binders
        return mempty
    <*> -- allow higher order binds?
        return False
    <*> -- allow higher order quals?
        return False
    <*> -- asserts
        return mempty
    <*> -- axiom environment
        return mempty
    <*> -- user defined data declarations
        return mempty
    <*> -- existential binds
        return mempty

-- | get the bind name used for the variable in the query
getFixpointName :: HornExpr -> Id
getFixpointName HVar {..} = varno <> prefix <> name
 where
  varno  = if hVarIndex > 0
           then "N" <> T.pack (show hVarIndex) <> "_"
           else ""
  prefix = getVarPrefix hVarType hVarRun
  name   = "M_" <> hVarModule <> "_V_" <> hVarName
getFixpointName _ = error "must be called with a variable"

getVarPrefix :: HornVarType -> HornVarRun -> Id
getVarPrefix hVarType hVarRun =
  case (hVarType, hVarRun) of
    (Tag  , LeftRun ) -> "VLT_"
    (Tag  , RightRun) -> "VRT_"
    (Value, LeftRun ) -> "VL_"
    (Value, RightRun) -> "VR_"

-- | update the state with the given fixpoint qualifier
addQualifier :: Member (State St) r => FT.Qualifier -> Sem r ()
addQualifier q = modify (& qualifiers %~ (|> q))

initialState :: St
initialState = St mempty mempty mempty mempty defaultQualifiers 0 0 mempty

-- | return the current constraint id and increment it later
freshConstraintId :: FD r => Sem r Integer
freshConstraintId =
  gets (^. constraintCounter) <* modify (& constraintCounter +~ 1)

-- | return the current qualifier id and increment it later
freshQualifierId :: Member (State St) r => Sem r Int
freshQualifierId =
  gets (^. qualifierCounter) <* modify (& qualifierCounter +~ 1)

instance FT.Loc HornClauseId where
  srcSpan _ = FT.dummySpan

instance FT.Fixpoint HornClauseId where
  toFix (HornClauseId n t) =
    PP.parens (FT.toFix t) PP.<+> PP.text "stmt id:" PP.<+> PP.int n

instance NFData HornClauseId

symbol :: Id -> FT.Symbol
symbol = FT.symbol

mkInt :: FT.Expr -> FT.SortedReft
mkInt e = FT.RR FT.intSort (FT.reft vSymbol e)

mkBool :: FT.Expr -> FT.SortedReft
mkBool e = FT.RR FT.boolSort (FT.reft vSymbol e)

throw :: Member (PE.Error IodineException) r => String -> Sem r a
throw = PE.throw . IE Query

-- | return combinations of the elements
twoPairs :: L a -> L (a, a)
twoPairs SQ.Empty      = mempty
twoPairs (a SQ.:<| as) = ((a, ) <$> as) <> twoPairs as

-- | make a KVar for the given invariant id
mkKVar :: Int -> FT.KVar
mkKVar n = FT.KV . FT.symbol $ "inv" <> show n

-- | variable used in refinements
vSymbol :: FT.Symbol
vSymbol = symbol "v"
