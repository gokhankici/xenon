{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Transform.Fixpoint.Common where

import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Horn
import           Iodine.Types

import           Control.DeepSeq
import           Control.Effect.Error
import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Effect.Trace
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import qualified Data.IntSet as IS
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           GHC.Generics hiding ( moduleName, to )
import qualified Language.Fixpoint.Types as FT
import qualified Text.PrettyPrint.HughesPJ as PP

-- -----------------------------------------------------------------------------
-- type definitions
-- -----------------------------------------------------------------------------

type A = Int
type M = Module A

type FInfo = FT.FInfo HornClauseId
type ModuleMap = HM.HashMap Id M

type G sig m = ( Has (Reader AnnotationFile) sig m
               , Has (Error IodineException) sig m
               , Has Trace sig m
               , Has (Reader ModuleMap) sig m
               , Has (Reader SummaryMap) sig m
               -- , Effect sig
               )

type FD sig m  = ( G sig m
                 , Has (State St) sig m
                 , Has (Reader HornVariableMap) sig m
                 )

type FDC sig m = ( FD sig m
                 , Has (State FT.IBindEnv) sig m
                 )

type QFD sig m = ( Has Trace sig m
                 , Has (Error IodineException) sig m
                 , Has (Reader M) sig m
                 , Has (State St) sig m
                 )
-- -----------------------------------------------------------------------------
-- solver state
-- -----------------------------------------------------------------------------

data HornClauseId = HornClauseId { hcStmtId :: Int, hcType :: HornType }
                  deriving (Show, Generic, Read)

data St = St { _hornConstraints           :: HM.HashMap Integer (FT.SubC HornClauseId)
             , _wellFormednessConstraints :: HM.HashMap FT.KVar (FT.WfC HornClauseId)
             , _bindEnvironment           :: FT.BindEnv
             , _globalConstantLiterals    :: FT.SEnv FT.Sort
             , _qualifiers                :: SQ.Seq FT.Qualifier

             , _constraintCounter         :: Integer
             , _qualifierCounter          :: Int
             , _invVarBindMap             :: HM.HashMap (Bool, HornExpr) (FT.BindId, FT.Expr)
             , _invConstBindMap           :: HM.HashMap HornExpr (FT.BindId, FT.Expr)
             }

makeLenses ''St

-- | We create a binding for true and false values, and use them in the horn
-- clauses instead of the boolean type directly.
setConstants :: FD sig m => m ()
setConstants = forM_ constants $ uncurry addConstBinding
 where
  b val = mkBool (FT.PIff (FT.eVar vSymbol) val)
  constants = [(HBool True, b FT.PTrue), (HBool False, b FT.PFalse)]


-- | return the id of the variable. if the variable does not exist, add it to
-- the environment first.
getVariableId :: FD sig m => Bool -> HornExpr -> m (FT.BindId, FT.Expr)
getVariableId isParam0 e0@HVar{..} = do
  mid <- gets (^. invVarBindMap . at (isParam, e))
  case mid of
    Just res  -> return res
    Nothing -> addBinding isParam e sr
  where
    isParam = isParam0 || hVarIndex == 0
    e = if isParam then HVar { hVarIndex = 0, .. } else e0
    sr = case hVarType of
           Value -> mkInt FT.PTrue
           Tag   -> mkBool FT.PTrue

getVariableId _ _ =
  error "unreachable"


addConstBinding :: FD sig m => HornExpr -> FT.SortedReft -> m ()
addConstBinding e sr = do
  let name = case e of
               HBool True  -> "tru"
               HBool False -> "fals"
               _           -> error "unreachable"
  be <- gets (^. bindEnvironment)
  let (n, be') = FT.insertBindEnv (symbol name) sr be
  modify $ (bindEnvironment .~ be')
         . (invConstBindMap . at e ?~ (n, FT.eVar name))


-- | add the variable name and its sort to the current bind environment
addBinding :: FD sig m => Bool -> HornExpr -> FT.SortedReft -> m (FT.BindId, FT.Expr)
addBinding isParam e sr = do
  be <- gets (^. bindEnvironment)
  let (n, be') = FT.insertBindEnv (symbol name) sr be
  let value = (n, FT.eVar name)
  modify $ (bindEnvironment .~ be')
         . (invVarBindMap . at (isParam, e) ?~ value)
  return value
  where name = getFixpointName isParam e


hornTypeToFP :: HornVarType -> (FT.Expr -> FT.Expr -> FT.Expr, FT.Sort)
hornTypeToFP t =
  case t of
    Value -> (FT.EEq, FT.intSort)
    Tag   -> (FT.PIff, FT.boolSort)


toFSort :: HornAppReturnType -> FT.Sort
toFSort HornInt  = FT.intSort
toFSort HornBool = FT.boolSort


-- | read the current state and create the query for the fixpoint solver
toFInfo :: FD sig m => m FInfo
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
getFixpointName :: Bool -> HornExpr -> Id
getFixpointName isParam HVar{..} =
  varno <> prefix
    <> varname <> "_" -- <>  modulename <> "_"
    <> threadno
  where
    varno = if isParam || hVarIndex == 0
            then ""
            else "N" <> T.pack (show hVarIndex) <> "_"
    prefix = getVarPrefix hVarType hVarRun
    varname = hVarName
    threadno = "T" <> T.pack (show hThreadId)
getFixpointName _ _ =
  error "unreachable"


getVarPrefix :: HornVarType -> HornVarRun -> Id
getVarPrefix hVarType hVarRun =
  case (hVarType, hVarRun) of
    (Tag  , LeftRun ) -> "TL_"
    (Tag  , RightRun) -> "TR_"
    (Value, LeftRun ) -> "VL_"
    (Value, RightRun) -> "VR_"


-- | update the state with the given fixpoint qualifier
addQualifier :: Has (State St) sig m => FT.Qualifier -> m ()
addQualifier q = modify (& qualifiers %~ (|> q))


-- | return the current constraint id and increment it later
freshConstraintId :: FD sig m => m Integer
freshConstraintId =
  gets (^. constraintCounter) <* modify (& constraintCounter +~ 1)


-- | return the current qualifier id and increment it later
freshQualifierId :: Has (State St) sig m => m Int
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


throw :: Has (Error IodineException) sig m => String -> m a
throw = throwError . IE Query


-- | make a KVar for the given invariant id
mkKVar :: Int -> FT.KVar
mkKVar n = FT.KV . FT.symbol $ "inv" <> show n


-- | variable used in refinements
vSymbol :: FT.Symbol
vSymbol = symbol "v"


allPredecessors :: Int
                -> G.Gr a b
                -> IS.IntSet
allPredecessors startNode g =
  go (SQ.fromList startParents) (IS.fromList startParents)
  where
    startParents = G.pre g startNode
    -- go :: worklist -> parents -> parents
    go :: L Int -> IS.IntSet -> IS.IntSet
    go SQ.Empty ps = ps
    go (n SQ.:<| wl) ps =
      let (wl', ps') =
            foldl'
            (\(acc_wl, acc_ps) preN ->
               if IS.member preN acc_ps
               then (acc_wl, acc_ps)
               else (acc_wl |> preN, IS.insert preN acc_ps))
            (wl, ps)
            (G.pre g n)
      in go wl' ps'


-- powerset :: L a -> L (L a)
-- powerset SQ.Empty            = SQ.Empty
-- powerset (a SQ.:<| SQ.Empty) = mempty |:> SQ.singleton a
-- powerset (a SQ.:<| as)       = let ps = powerset as
--                                in ps <> ((a SQ.:<|) <$> ps)
