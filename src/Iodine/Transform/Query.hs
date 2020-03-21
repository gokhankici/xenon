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

import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Horn
import           Iodine.Transform.VCGen
import           Iodine.Transform.VariableRename (nonInputPrefix)
import           Iodine.Types
import           Iodine.Utils

import           Control.DeepSeq
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.List (nub)
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           GHC.Generics hiding ( moduleName, to )
import qualified Language.Fixpoint.Types as FT
import           Polysemy
import qualified Polysemy.Error as PE
import           Polysemy.Reader
import           Polysemy.State
import qualified Polysemy.Trace as PT
import qualified Text.PrettyPrint.HughesPJ as PP
-- import           Text.Printf

-- -----------------------------------------------------------------------------
-- type definitions
-- -----------------------------------------------------------------------------

type FInfo = FT.FInfo HornClauseId
type ModuleMap = HM.HashMap Id (Module Int)

type G r   = Members '[ Reader AnnotationFile
                      , PE.Error IodineException
                      , PT.Trace
                      , Reader ModuleMap
                      , Reader SummaryMap
                      ] r

type FD r  = ( G r
             , Members '[ State St
                        , Reader HornVariableMap
                        ] r
             )

type FDC r = ( FD r
             , Member (State FT.IBindEnv) r
             )

type QFD r = Members '[ PT.Trace
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

initialState :: St
initialState = St mempty mempty mempty mempty defaultQualifiers 0 0 mempty

-- -----------------------------------------------------------------------------
-- generate a query for the liquid-fixpoint solver
-- -----------------------------------------------------------------------------

-- | Given the verification conditions, generate the query to be sent to the
-- fixpoint solver
constructQuery :: G r => L (Module Int) -> VCGenOutput -> Sem r FInfo
constructQuery modules (hvs, horns) = runReader hvs $ evalState initialState $ do
  setConstants
  traverse_ generateConstraint horns
  for_ modules $ \m@Module{..} -> do
    generateWFConstraints m
    (getQualifiers moduleName >>= traverse_ generateQualifiers) & runReader m
    topModuleName <- asks (view afTopModule)
    unless (moduleName == topModuleName) $
      addSummaryQualifiers m
    simpleCheck <- isModuleSimple m
    when simpleCheck $
      addSimpleModuleQualifiers m
  ask >>= generateAutoQualifiers
  toFInfo


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
  generateWFConstraint moduleName m
  traverse_ (generateWFConstraint moduleName) alwaysBlocks


-- | Create a well formedness constraint for the given statement
generateWFConstraint :: (FD r, MakeKVar t)
                     => Id      -- ^ module name
                     -> t Int
                     -> Sem r ()
generateWFConstraint threadModuleName thread = do
  varNames <- askHornVariables thread
  let hornVars = setThreadId thread
                 <$> foldMap (`allHornVars` threadModuleName) varNames
  (ienv,_) <- traverse_ convertExpr hornVars & runState mempty
  case FT.wfC ienv (mkInt e) md of
    [wf] -> modify ((wellFormednessConstraints . at kvar) ?~ wf)
    wfcs -> throw $ "did not get only 1 wfc: " ++ show wfcs
 where
  tid    = getThreadId thread
  kvar   = mkKVar tid
  e      = FT.PKVar kvar mempty
  md     = HornClauseId tid WellFormed

-- -----------------------------------------------------------------------------
-- HornExpr -> FT.Expr
-- -----------------------------------------------------------------------------

-- | return the fixpoint name of the variable after updating the current bind
-- environment
convertHVar :: FDC r => Bool -> HornExpr -> Sem r FT.Expr
convertHVar isParam var@HVar{..} = do
  n <- getVariableId isParam var
  modify (FT.insertsIBindEnv [n])
  return $ FT.eVar (getFixpointName isParam var)
convertHVar _ _ =
  throw "convertHVar must be called with a Horn variable"

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

convertExpr var@HVar{} = convertHVar False var

convertExpr (HAnd es) =
  case es of
    SQ.Empty -> convertExpr (HBool True)
    _        -> FT.PAnd . toList <$> traverse convertExpr es

convertExpr (HOr es) =
  case es of
    SQ.Empty -> convertExpr (HBool False)
    _        -> FT.POr . toList <$> traverse convertExpr es

convertExpr HBinary {..} =
  toFP <$> convertExpr hBinaryLhs <*> convertExpr hBinaryRhs
  where
    toFP =
        case hBinaryOp of
          HEquals    -> FT.EEq
          HNotEquals -> FT.PAtom FT.Ne
          HImplies   -> FT.PImp
          HIff       -> FT.PIff

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
          then FT.mkFFunc 0 $ replicate arity FT.intSort ++ [ret]
          else ret

convertExpr KVar {..} =
  FT.PKVar (mkKVar hKVarId) . FT.mkSubst . toList <$>
  traverse
  (\(lhs, rhs) -> do
      lhs' <- convertHVar True lhs
      sym  <-
        case lhs' of
          FT.EVar v -> return v
          _ -> throw $ "expecting lhs of kvar substitution to be a symbol: " ++ show lhs
      rhs' <- convertExpr rhs
      return (sym, rhs')
  )
  hKVarSubs


-- | return the id of the variable. if the variable does not exist, add it to
-- the environment first.
getVariableId :: FD r => Bool -> HornExpr -> Sem r FT.BindId
getVariableId isParam v = do
  mid <- HM.lookup name <$> gets (^. invBindMap)
  case mid of
    Just n  -> return n
    Nothing -> addBinding name sr
 where
  name = getFixpointName isParam v
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

-- | if all inputs are ct and some of them are public, define the output color
addSimpleModuleQualifiers :: FD r => Module Int -> Sem r ()
addSimpleModuleQualifiers m =
  (zip [0..] <$> asks (HM.toList . portDependencies . (HM.! moduleName m))) >>=
    traverse_
    (\(n1, (o, inputSet)) -> do
       let inputSeq = toSequence inputSet
           inputList = toList inputSet
       flip SQ.traverseWithIndex (powerset inputSeq) $ \n2 vs ->
         for_ [Tag, Value] $ \t ->
         let name = "SimpleModule_" <> T.unpack (moduleName m) <> "_" <> show n1 <> "_" <> show n2 <> "_" <> show t
         in addQualifier $
            mkSimpleModuleQualifierHelper m name inputList (toList vs) o t
    )


mkSimpleModuleQualifierHelper :: Module Int -> String -> [Id] -> [Id] -> Id -> HornVarType -> FT.Qualifier
mkSimpleModuleQualifierHelper m qualifierName inputs valEqInputs rhsName rhsType =
  FT.mkQual
  (FT.symbol qualifierName)
  ([ FT.QP vSymbol FT.PatNone FT.FInt
   , FT.QP (symbol "rl") (FT.PatExact $ mkRhsSymbol LeftRun)  rt
   , FT.QP (symbol "rr") (FT.PatExact $ mkRhsSymbol RightRun) rt
   ] ++
   concat [ [ FT.QP (FT.symbol $ "it" ++ show n2)     (FT.PatExact $ mkLhsSymbol i Tag LeftRun)  bt
            , FT.QP (FT.symbol $ "it" ++ show (n2+1)) (FT.PatExact $ mkLhsSymbol i Tag RightRun) bt
            ]
          | (i, n2) <- zip inputs [0,2..]
          ] ++
   concat [ [ FT.QP (FT.symbol $ "iv" ++ show n2)     (FT.PatExact $ mkLhsSymbol i Value LeftRun)  it
            , FT.QP (FT.symbol $ "iv" ++ show (n2+1)) (FT.PatExact $ mkLhsSymbol i Value RightRun) it
            ]
          | (i, n2) <- zip valEqInputs [0,2..]
          ]
  )
  (FT.PAnd lhsExprs `FT.PImp` rhsExpr)
  (FT.dummyPos "")
  where
    rhsExpr =
      case rhsType of
        Tag   -> FT.PAnd $ rhsEq:rhsTagDefs
        Value -> rhsEq
    (fpop, rt) = hornTypeToFP rhsType
    inputLen = length inputs
    rhsEq = FT.eVar @String "rl" `fpop`  FT.eVar @String "rr"
    rhsTagDefs =
      [ let isLeft = t == LeftRun
        in FT.eVar @String (if isLeft then "rl" else "rl")
           `fpop`
           FT.POr [ FT.eVar ("it" ++ show (if isLeft then n2 else n2 + 1))
                  | n2 <- take inputLen [0,2..]
                  ]
      | t <- [LeftRun, RightRun]
      ]
    lhsExprs =
      [ FT.eVar ("it" ++ show n2) `FT.PIff` FT.eVar ("it" ++ show (n2+1))
      | (_, n2) <- zip inputs [0,2..]
      ] ++
      [ FT.eVar ("iv" ++ show n2) `FT.EEq` FT.eVar ("iv" ++ show (n2+1))
      | (_, n2) <- zip valEqInputs [0,2..]
      ]
    mkRhsSymbol r = symbol $ getFixpointName True $ mkVar rhsName rhsType r
    mkLhsSymbol v t r = symbol $ getFixpointName True $ mkVar v t r
    mkVar v t r = setThreadId m $ HVar0 v (moduleName m) t r
    bt = FT.boolSort
    it = FT.intSort
{- HLINT ignore mkSimpleModuleQualifierHelper -}

hornTypeToFP :: HornVarType -> (FT.Expr -> FT.Expr -> FT.Expr, FT.Sort)
hornTypeToFP t =
  case t of
    Value -> (FT.EEq, FT.intSort)
    Tag   -> (FT.PIff, FT.boolSort)


-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------


addSummaryQualifiers :: FD r => Module Int -> Sem r ()
addSummaryQualifiers m@Module{..} = do
  mSummary <- asks (HM.lookup moduleName)
  let inputLists = filter (not . HS.null) . nub . concatMap (HM.elems . portDependencies)
                   $ mSummary
  for_ (zip inputLists [0..]) $ \(ls, n) -> do
    let inputSeq  = toSequence ls
    addSummaryQualifiersKVar m moduleName (show n) inputSeq
    trace "addSummaryQualifiersKVar" (getThreadId m, inputSeq)
  for_ alwaysBlocks $ \ab -> do
    let readVariables = getReadOnlyVariables (abStmt ab)
        readVariablesSeq = toSequence readVariables
    trace "addSummaryQualifiersKVar" (getThreadId ab, readVariables)
    flip SQ.traverseWithIndex (powerset readVariablesSeq) $ \n inputSeq ->
      addSummaryQualifiersKVar ab moduleName (show n) inputSeq



addSummaryQualifiersKVar :: (FD r, MakeKVar k)
                         => k Int  -- ^ always block or module
                         -> Id     -- ^ module name
                         -> String -- ^ qualifier name suffix
                         -> L Id   -- ^ input list
                         -> Sem r ()
addSummaryQualifiersKVar kv moduleName qualifierSuffix inputSeq = do
  let inputList = toList inputSeq
      ps = powerset inputSeq
  flip SQ.traverseWithIndex ps $ \n vs -> do
    let vsList = toList vs
        name = "SummaryQualifier_"
               <> T.unpack moduleName <> "_"
               <> "T" <> show (getThreadId kv) <> "_"
               <> show n
    addQualifier $
      mkSummaryQualifierHelper kv moduleName (name <> "_Tag_" <> qualifierSuffix)
      inputList vsList Tag
    addQualifier $
      mkSummaryQualifierHelper kv moduleName (name <> "_Value_" <> qualifierSuffix)
      inputList vsList Value
  return ()


-- | given a list of input ports i1, i2, ... creates a qualifier of the form:
-- ((TL_i1 <=> TR_i1) && (TL_i2 <=> TR_i2) && ...) ==> TL_$1 <=> TR_$1)
mkSummaryQualifierHelper :: MakeKVar k
                         => k Int       -- ^ always block or module
                         -> Id          -- ^ module name
                         -> String      -- ^ qualifier name
                         -> [Id]        -- ^ inputs
                         -> [Id]        -- ^ always_equal inputs
                         -> HornVarType -- ^ type of the right hand side
                         -> FT.Qualifier
mkSummaryQualifierHelper kv moduleName qualifierName inputs valEqInputs rhsType =
  FT.mkQual
  (FT.symbol qualifierName)
  ([ FT.QP vSymbol FT.PatNone FT.FInt
   , FT.QP (symbol "rl") (FT.PatPrefix (mkRhsSymbol rhsType LeftRun) 0)  rt
   , FT.QP (symbol "rr") (FT.PatPrefix (mkRhsSymbol rhsType RightRun) 0) rt
   ] ++
   concat [ [ FT.QP (FT.symbol $ "it" ++ show n2)     (FT.PatExact $ mkLhsSymbol i Tag LeftRun)  bt
            , FT.QP (FT.symbol $ "it" ++ show (n2+1)) (FT.PatExact $ mkLhsSymbol i Tag RightRun) bt
            ]
          | (i, n2) <- zip inputs [0,2..]
          ] ++
   concat [ [ FT.QP (FT.symbol $ "iv" ++ show n2)     (FT.PatExact $ mkLhsSymbol i Value LeftRun)  it
            , FT.QP (FT.symbol $ "iv" ++ show (n2+1)) (FT.PatExact $ mkLhsSymbol i Value RightRun) it
            ]
          | (i, n2) <- zip valEqInputs [0,2..]
          ]
  )
  (FT.PAnd lhsExprs `FT.PImp` (FT.eVar @String "rl" `fpop`  FT.eVar @String "rr"))
  (FT.dummyPos "")
  where
    (fpop, rt) = hornTypeToFP rhsType
    lhsExprs =
      [ FT.eVar ("it" ++ show n2) `FT.PIff` FT.eVar ("it" ++ show (n2+1))
      | (_, n2) <- zip inputs [0,2..]
      ] ++
      [ FT.eVar ("iv" ++ show n2) `FT.EEq` FT.eVar ("iv" ++ show (n2+1))
      | (_, n2) <- zip valEqInputs [0,2..]
      ]
    mkRhsSymbol t r =
      symbol $ getFixpointNonInputVarPrefix t r
    mkLhsSymbol v t r =
      symbol $
      getFixpointName True $
      mkVar v t r
    mkVar v t r =
      setThreadId kv $ HVar0 v moduleName t r
    bt = FT.boolSort
    it = FT.intSort

powerset :: L a -> L (L a)
powerset SQ.Empty            = SQ.Empty
powerset (a SQ.:<| SQ.Empty) = mempty |:> SQ.singleton a
powerset (a SQ.:<| as)       = let ps = powerset as
                               in ps <> ((a SQ.:<|) <$> ps)


-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------
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
  (varPairs <$> asks moduleName) >>=
  traverse_ (\pair ->
               (q pair <$> freshQualifierId) >>=
               addQualifier)
 where
  vars m       = (`HVarTL0` m) <$> vs
  varPairs m   = twoPairs $ getFixpointName True <$> vars m
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
            lhs FT.PIff rhss
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
    (FT.symbol @String ("TagZero" ++ show n))
    [ FT.QP vSymbol FT.PatNone FT.FInt
    , FT.QP (symbol "x")
            (FT.PatPrefix (symbol $ getVarPrefix Tag r) 1)
            (FT.FTC FT.boolFTyCon)
    ]
    (FT.PIff (FT.eVar @Id "x") FT.PFalse)
    (FT.dummyPos "")


-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------


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
    mkVar v     = getFixpointName True $ HVarTL0 v topModuleName


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

-- -----------------------------------------------------------------------------
-- helper functions
-- -----------------------------------------------------------------------------

-- | We create a binding for true and false values, and use them in the horn
-- clauses instead of the boolean type directly.
setConstants :: FD r => Sem r ()
setConstants = forM_ constants $ uncurry addBinding
 where
  b val = mkBool (FT.PIff (FT.eVar vSymbol) val)
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
-- varno <> type prefix <> varname <> modulename <> threadno
getFixpointName, getFixpointVarPrefix, getFixpointTypePrefix  :: Bool -> HornExpr -> Id
getFixpointName isParam v =
  getFixpointVarPrefix isParam v <> threadno
  where
    threadno = "T" <> T.pack (show $ hThreadId v)
getFixpointVarPrefix isParam v =
  getFixpointTypePrefix isParam v <> varname <> "_" <>  modulename <> "_"
  where
    modulename = "M_" <> hVarModule v
    varname = "V_" <> hVarName v
getFixpointTypePrefix isParam v =
  varno <> prefix
  where
    varno = if isParam || hVarIndex v == 0
            then ""
            else "N" <> T.pack (show $ hVarIndex v) <> "_"
    prefix = getVarPrefix (hVarType v) (hVarRun v)

getFixpointNonInputVarPrefix :: HornVarType -> HornVarRun -> Id
getFixpointNonInputVarPrefix t r = getVarPrefix t r <> "V_" <> nonInputPrefix

getVarPrefix :: HornVarType -> HornVarRun -> Id
getVarPrefix hVarType hVarRun =
  case (hVarType, hVarRun) of
    (Tag  , LeftRun ) -> "TL_"
    (Tag  , RightRun) -> "TR_"
    (Value, LeftRun ) -> "VL_"
    (Value, RightRun) -> "VR_"

-- | update the state with the given fixpoint qualifier
addQualifier :: Member (State St) r => FT.Qualifier -> Sem r ()
addQualifier q = modify (& qualifiers %~ (|> q))

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

-- | make a KVar for the given invariant id
mkKVar :: Int -> FT.KVar
mkKVar n = FT.KV . FT.symbol $ "inv" <> show n

-- | variable used in refinements
vSymbol :: FT.Symbol
vSymbol = symbol "v"
