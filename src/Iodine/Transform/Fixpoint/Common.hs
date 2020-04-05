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

module Iodine.Transform.Fixpoint.Common where

import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Horn
import           Iodine.Transform.VCGen
import           Iodine.Types

import           Control.DeepSeq
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
import           Polysemy
import qualified Polysemy.Error as PE
import           Polysemy.Reader
import           Polysemy.State
import qualified Polysemy.Trace as PT
import qualified Text.PrettyPrint.HughesPJ as PP

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

-- | We create a binding for true and false values, and use them in the horn
-- clauses instead of the boolean type directly.
setConstants :: FD r => Sem r ()
setConstants = forM_ constants $ uncurry addBinding
 where
  b val = mkBool (FT.PIff (FT.eVar vSymbol) val)
  constants = [("tru", b FT.PTrue), ("fals", b FT.PFalse)]


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


hornTypeToFP :: HornVarType -> (FT.Expr -> FT.Expr -> FT.Expr, FT.Sort)
hornTypeToFP t =
  case t of
    Value -> (FT.EEq, FT.intSort)
    Tag   -> (FT.PIff, FT.boolSort)


toFSort :: HornAppReturnType -> FT.Sort
toFSort HornInt  = FT.intSort
toFSort HornBool = FT.boolSort


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
  getFixpointTypePrefix isParam v <> varname <> "_" -- <>  modulename <> "_"
  where
    -- modulename = "M_" <> hVarModule v
    varname = "V_" <> hVarName v
getFixpointTypePrefix isParam v =
  varno <> prefix
  where
    varno = if isParam || hVarIndex v == 0
            then ""
            else "N" <> T.pack (show $ hVarIndex v) <> "_"
    prefix = getVarPrefix (hVarType v) (hVarRun v)


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
