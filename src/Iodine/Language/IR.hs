{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE StrictData        #-}

module Iodine.Language.IR
  ( Expr (..)
  , AssignmentType (..)
  , Stmt (..)
  , ModuleInstance (..)
  , Module (..)
  , Port (..)
  , Variable (..)
  , Event (..)
  , AlwaysBlock (..)
  , Thread (..)
  , GetVariables (..)
  , GetData (..)
  , UFOp (..)
  , isAB
  , isInput
  , isStar
  , isVariable
  , moduleInputs
  , moduleAllInputs
  , moduleInstanceReadsAndWrites
  , moduleOutputs
  , getReadOnlyVariables
  , getUpdatedVariables
  , DocColor (..)
  , DocConfig (..)
  , colorId
  , prettyShow
  )
where

import           Iodine.Language.Annotation
import           Iodine.Types
import           Iodine.Utils

import           Control.Lens hiding (op)
import           Data.Foldable
import           Data.Functor (void)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Hashable
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           GHC.Generics hiding (moduleName)
import           Polysemy
import           Polysemy.Reader
import           Polysemy.State
import qualified Text.PrettyPrint as PP

data Variable =
    Wire     { variableName :: Id }
  | Register { variableName :: Id }
  deriving (Eq)

data Port =
    Input  { portVariable :: Variable }
  | Output { portVariable :: Variable }
  deriving (Eq)

data Expr a =
  Constant { constantValue :: Id
           , exprData      :: a
           }
  | Variable { varName       :: Id
             , varModuleName :: Id
             , exprData      :: a
             }
  | UF { ufOp     :: UFOp
       , ufArgs   :: L (Expr a)
       , exprData :: a
       }
  | IfExpr { ifExprCondition :: Expr a
           , ifExprThen      :: Expr a
           , ifExprElse      :: Expr a
           , exprData        :: a
           }
  | Str { strValue :: Id
        , exprData :: a
        }
  | Select { selectVar     :: Expr a
           , selectIndices :: L (Expr a)
           , exprData      :: a
           }
  deriving (Eq, Generic, Functor, Foldable, Traversable)

data UFOp =
    UF_abs
  | UF_and
  | UF_negate
  | UF_negative
  | UF_not
  | UF_add
  | UF_or
  | UF_arith_rs
  | UF_bitwise_and
  | UF_bitwise_or
  | UF_case_eq
  | UF_case_neq
  | UF_div
  | UF_exp
  | UF_ge
  | UF_gt
  | UF_le
  | UF_logic_eq
  | UF_logic_neq
  | UF_lt
  | UF_mod
  | UF_mul
  | UF_nand
  | UF_nor
  | UF_shl
  | UF_shr
  | UF_sub
  | UF_xnor
  | UF_xor
  | UF_concat
  | UF_write_to_index
  | UF_call Id -- ^ call a function with the given name
  deriving (Eq)
{- HLINT ignore UFOp -}

data AssignmentType = Blocking | NonBlocking | Continuous
                    deriving (Generic, Eq, Show)

data ModuleInstance a =
  ModuleInstance { moduleInstanceType  :: Id
                 , moduleInstanceName  :: Id
                 , moduleInstancePorts :: HM.HashMap Id (Expr a)
                 , moduleInstanceData  :: a
                 }
  deriving (Generic, Functor, Foldable, Traversable)

data Stmt a =
  Block { blockStmts :: L (Stmt a)
        , stmtData   :: a
        }
  | Assignment { assignmentType :: AssignmentType
               , assignmentLhs  :: Expr a
               , assignmentRhs  :: Expr a
               , stmtData       :: a
               }
  | IfStmt   { ifStmtCondition :: Expr a
             , ifStmtThen      :: Stmt a
             , ifStmtElse      :: Stmt a
             , stmtData        :: a
             }
  | Skip { stmtData :: a }
  deriving (Generic, Functor, Foldable, Traversable)

data Event a =
    PosEdge { eventExpr :: Expr a }
  | NegEdge { eventExpr :: Expr a }
  | Star
  deriving (Generic, Functor, Foldable, Traversable, Eq)

data AlwaysBlock a =
    AlwaysBlock { abEvent :: Event a
                , abStmt  :: Stmt a
                , abData  :: a
                }
  deriving (Generic, Functor, Foldable, Traversable)

data Module a =
  Module { moduleName      :: Id
         , ports           :: L Port
         , variables       :: L Variable
         , constantInits   :: L (Id, Expr a)
         , gateStmts       :: L (Stmt a)
         , alwaysBlocks    :: L (AlwaysBlock a)
         , moduleInstances :: L (ModuleInstance a)
         , moduleData      :: a
         }
  deriving (Generic, Functor, Foldable, Traversable)

-- | An always block or a module instance
data Thread a = AB (AlwaysBlock a)
              | MI (ModuleInstance a)

class GetVariables m where
  -- return the name of the variables in type m
  getVariables :: m a -> HS.HashSet Id

instance GetVariables Stmt where
  getVariables = \case
    Block {..}          -> mfold getVariables blockStmts
    Assignment {..}     -> mfold getVariables [assignmentLhs, assignmentRhs]
    IfStmt {..}         -> getVariables ifStmtCondition <> mfold getVariables [ifStmtThen, ifStmtElse]
    Skip {..}           -> mempty

instance GetVariables Expr where
  getVariables = \case
    Variable {..} -> HS.singleton varName
    Constant {..} -> mempty
    UF {..}       -> mfold getVariables ufArgs
    IfExpr {..}   -> mfold getVariables [ifExprCondition, ifExprThen, ifExprElse]
    Str {..}      -> mempty
    Select {..}   -> mfold getVariables $ selectVar SQ.<| selectIndices

instance GetVariables ModuleInstance where
  getVariables ModuleInstance{..} =
    foldMap getVariables $ HM.elems moduleInstancePorts

instance GetVariables AlwaysBlock where
  getVariables AlwaysBlock{..} = getVariables abStmt

instance GetVariables Thread where
  getVariables (AB ab) = getVariables ab
  getVariables (MI mi) = getVariables mi

instance GetVariables Module where
  getVariables Module{..} =
    foldl' (flip HS.insert) mempty (variableName . portVariable <$> ports)

class GetData m where
  getData :: m a -> a

instance GetData Expr where
  getData = exprData

instance GetData ModuleInstance where
  getData = moduleInstanceData

instance GetData AlwaysBlock where
  getData = abData

instance GetData Thread where
  getData (AB ab) = getData ab
  getData (MI mi) = getData mi

instance GetData Module where
  getData = moduleData

-- -----------------------------------------------------------------------------
-- Typeclass Instances
-- -----------------------------------------------------------------------------
class ShowIndex a where
  showIndex :: a -> String

instance ShowIndex () where
  showIndex () = ""

instance ShowIndex Int where
  showIndex n  =
    if n > 0
    then " #" ++ show n
    else ""

docIndex :: ShowIndex a => a -> PP.Doc
docIndex = PP.text . showIndex

data DocColor = Red | Blue | Green

colorId :: DocColor -> Id -> String
colorId c v = "\x1b[1m" <> colorPrefix <> s <> "\x1b[0m"
  where
    colorPrefix =
      case c of
        Red   -> "\x1b[31m"
        Blue  -> "\x1b[34m"
        Green -> "\x1b[32m"
    s = T.unpack v

newtype DocConfig = DocConfig
  { varColorMap :: HM.HashMap Id DocColor }

defaultDocConfig :: DocConfig
defaultDocConfig = DocConfig mempty

class Doc a where
  doc ::DocConfig -> a -> PP.Doc

sep :: PP.Doc
sep = PP.comma

docList :: Doc a => DocConfig -> L a -> PP.Doc
docList c l = PP.hsep $ PP.punctuate sep (doc c <$> toList l)

nest :: PP.Doc -> PP.Doc
nest = PP.nest 2

vcat :: Doc a => DocConfig -> L a -> PP.Doc
vcat c = PP.vcat . fmap (doc c) . toList

id2Doc :: Id -> PP.Doc
id2Doc = PP.text . T.unpack

instance Doc Variable where
  doc _ (Wire v)     = PP.text "wire" PP.<+> id2Doc v PP.<> PP.semi
  doc _ (Register v) = PP.text "reg " PP.<+> id2Doc v PP.<> PP.semi

instance Doc Port where
  doc _ (Input p)  = PP.text "input " PP.<+> id2Doc (variableName p) PP.<> PP.semi
  doc _ (Output p) = PP.text "output" PP.<+> id2Doc (variableName p) PP.<> PP.semi

instance Doc UFOp where
  doc _ = PP.text . \case
    UF_abs            -> "uf_abs"
    UF_and            -> "uf_and"
    UF_negate         -> "uf_negate"
    UF_negative       -> "uf_negative"
    UF_not            -> "uf_not"
    UF_add            -> "uf_add"
    UF_or             -> "uf_or"
    UF_arith_rs       -> "uf_arith_rs"
    UF_bitwise_and    -> "uf_bitwise_and"
    UF_bitwise_or     -> "uf_bitwise_or"
    UF_case_eq        -> "uf_case_eq"
    UF_case_neq       -> "uf_case_neq"
    UF_div            -> "uf_div"
    UF_exp            -> "uf_exp"
    UF_ge             -> "uf_ge"
    UF_gt             -> "uf_gt"
    UF_le             -> "uf_le"
    UF_logic_eq       -> "uf_logic_eq"
    UF_logic_neq      -> "uf_logic_neq"
    UF_lt             -> "uf_lt"
    UF_mod            -> "uf_mod"
    UF_mul            -> "uf_mul"
    UF_nand           -> "uf_nand"
    UF_nor            -> "uf_nor"
    UF_shl            -> "uf_shl"
    UF_shr            -> "uf_shr"
    UF_sub            -> "uf_sub"
    UF_xnor           -> "uf_xnor"
    UF_xor            -> "uf_xor"
    UF_concat         -> "uf_concat"
    UF_write_to_index -> "uf_write_to_index"
    UF_call f         -> "uf_call_function_" <> T.unpack f

instance ShowIndex a => Doc (Expr a) where
  doc _ (Constant c _)   = id2Doc c
  doc cfg (Variable v _ a) = str PP.<> docIndex a
    where str = case HM.lookup v $ varColorMap cfg of
                  Nothing -> id2Doc v
                  Just dc -> PP.text $ colorId dc v

  doc cfg (UF n es _)      = doc cfg n PP.<> PP.parens (docList cfg es)
  doc cfg (IfExpr c t e _) = PP.parens $ PP.hsep [doc cfg c, PP.text "?", doc cfg t, PP.colon, doc cfg e]
  doc _   (Str s _)        = PP.quotes $ id2Doc s
  doc cfg (Select v is _)  = doc cfg v PP.<> PP.brackets (docList cfg is)

instance ShowIndex a => Doc (Event a) where
  doc c (PosEdge e) = PP.text "@(posedge " PP.<> doc c e PP.<> PP.rparen
  doc c (NegEdge e) = PP.text "@(negedge " PP.<> doc c e PP.<> PP.rparen
  doc _ Star        = PP.text "@(*)"

instance ShowIndex a => Doc (Stmt a) where
  doc cfg (Block ss a) =
    case ss of
      SQ.Empty          -> doc cfg (Skip a)
      s SQ.:<| SQ.Empty -> doc cfg s
      _                 -> PP.lbrace PP.$+$
                           nest (vcat cfg ss) PP.$+$
                           PP.rbrace
  doc cfg (Assignment t l r _) =
    doc cfg l PP.<+> PP.text op PP.<+> doc cfg r PP.<> PP.semi
    where op = case t of
                 Blocking    -> "="
                 NonBlocking -> "<="
                 Continuous  -> ":="
  doc cfg (IfStmt c t e _) =
    PP.cat [ PP.text "if" PP.<+> PP.parens (doc cfg c) PP.<+> PP.lbrace
           , nest $ doc cfg t
           , PP.rbrace PP.<+> PP.text "else" PP.<+> PP.lbrace
           , nest $ doc cfg e
           , PP.rbrace
           ]
  doc _ (Skip _) = PP.text "skip" PP.<> PP.semi

instance ShowIndex a => Doc (ModuleInstance a) where
  doc c (ModuleInstance t n ps a) =
    id2Doc t PP.<+> id2Doc n PP.<> PP.parens (PP.hsep $ PP.punctuate sep args) PP.<> docIndex a
    where
      args = docArgs ps
      docArgs =
        HM.foldlWithKey'
        (\acc v e-> (id2Doc v PP.<+> PP.equals PP.<+> doc c e) : acc)
        []

instance ShowIndex a => Doc (AlwaysBlock a) where
  doc c (AlwaysBlock e s a) =
    PP.sep [ PP.text "always"
             PP.<> PP.text (showIndex a)
             PP.<+> doc c e
           , doc c s
           ]

instance ShowIndex a => Doc (Module a) where
  doc c Module{..} =
    PP.vcat [ PP.text "module" PP.<> docIndex moduleData PP.<+> id2Doc moduleName PP.<> PP.parens args PP.<> PP.semi
            , PP.nest 2 contents
            , PP.text "endmodule"
            ]
    where
      contents =
        vcatNL [ vcat c ports
               , vcat c variables
               , vcatNS gateStmts
               , vcatNS moduleInstances
               , vcatNS alwaysBlocks
               ]
      args =
        PP.hsep $
        PP.punctuate sep (id2Doc . variableName . portVariable <$> toList ports)

      vcatNS :: Doc b => L b -> PP.Doc
      vcatNS = vcatNL . fmap (doc c) . toList

      vcatNL :: [PP.Doc] -> PP.Doc
      vcatNL = PP.vcat . go . filter (not . PP.isEmpty)
        where
          go []     = []
          go [a]    = [a]
          go (a:as) = a : PP.text "" : go as

prettyShow :: Doc a => DocConfig -> a -> String
prettyShow cfg = PP.render . doc cfg

instance Hashable a => Hashable (Expr a) where
  hashWithSalt n (Variable v m a) = hashWithSalt n (v,m,a)
  hashWithSalt _ _                = notSupported

instance Hashable a => Hashable (Event a) where
  hashWithSalt n (PosEdge e) = hashWithSalt n (1::Int, e)
  hashWithSalt n (NegEdge e) = hashWithSalt n (2::Int, e)
  hashWithSalt n Star        = hashWithSalt n (3::Int)

instance Show Variable where
  show (Register r) = "reg(" ++ T.unpack r ++ ")"
  show (Wire w)     = "wire(" ++ T.unpack w ++ ")"

instance Show Port where
  show (Input i)  = "input(" ++ show i ++ ")"
  show (Output o) = "output(" ++ show o ++ ")"

instance ShowIndex a => Show (Event a) where
  show = PP.render . doc defaultDocConfig

instance ShowIndex a => Show (Stmt a) where
  show = PP.render . doc defaultDocConfig

instance Show UFOp where
  show = PP.render . doc defaultDocConfig

instance ShowIndex a => Show (Expr a) where
  show = PP.render . doc defaultDocConfig

instance ShowIndex a => Show (AlwaysBlock a) where
  show = PP.render . doc defaultDocConfig

instance ShowIndex a => Show (Module a) where
  show = PP.render . doc defaultDocConfig

instance ShowIndex a => Show (ModuleInstance a) where
  show = PP.render . doc defaultDocConfig

instance ShowIndex a => Show (Thread a) where
  show (AB ab) = PP.render $ doc defaultDocConfig ab
  show (MI mi) = PP.render $ doc defaultDocConfig mi

isInput :: Port -> Bool
isInput (Input _)  = True
isInput (Output _) = False

-- | given a module and a set of clocks, return the input/output port names of
-- that module
moduleInputs, moduleOutputs :: Module a -> Ids -> Ids
(moduleInputs, moduleOutputs) = (helper True, helper False)
  where
    helper check Module{..} mclks =
      foldl' (addInput check mclks) mempty ports
    addInput check mclks acc p =
      let v = variableName (portVariable p)
          notClk = v `notElem` mclks
      in if isInput p == check && notClk
         then HS.insert v acc
         else acc

moduleAllInputs :: Module a -> Ids
moduleAllInputs m = moduleInputs m mempty

-- | given a module, module's clocks and an instance of it, returns the
-- variables that are read and written by the instance.
moduleInstanceReadsAndWrites :: Module a -> Ids -> ModuleInstance a -> (Ids, Ids)
moduleInstanceReadsAndWrites m mClks mi = run $ execState (mempty, mempty) $ do
  for_ miInputs $ \inputPort ->
    for_ (getVariables $ moduleInstancePorts mi HM.! inputPort) $ \v ->
    modify (_1 %~ HS.insert v)
  for_ miOutputs $ \outputPort -> do
    let portExpr    = moduleInstancePorts mi HM.! outputPort
        updatedVars = getUpdatedVars portExpr
        readVars    = getVariables portExpr `HS.difference` updatedVars
    for_ readVars    $ \v -> modify (_1 %~ HS.insert v)
    for_ updatedVars $ \v -> modify (_2 %~ HS.insert v)
  where
    miInputs = moduleInputs m mClks
    miOutputs = moduleOutputs m mClks

    getUpdatedVars = \case
      Variable{..}  -> HS.singleton varName
      Constant {..} -> mempty
      e@UF {}       -> error
                       $ unlines [ "Module instance output port expression is an uninterpreted function!"
                                 , show $ void e
                                 ]
      IfExpr {..}   -> mfold getUpdatedVars [ifExprThen, ifExprElse]
      Str {..}      -> mempty
      Select {..}   -> getUpdatedVars selectVar


-- | is the given thread an always block with the star event?
isStar :: AlwaysBlock a -> Bool
isStar ab = case abEvent ab of
              Star -> True
              _    -> False

isVariable :: Expr a -> Bool
isVariable Variable{} = True
isVariable _ = False

isAB :: Thread a -> Bool
isAB (AB _) = True
isAB (MI _) = False

getReadOnlyVariables :: Stmt a -> Ids
getReadOnlyVariables s =
  let (readVars, writtenVars) = go s & execState (mempty, mempty) & run
  in readVars `HS.difference` writtenVars
  where
    go :: Stmt a -> Sem '[State (Ids, Ids)] ()
    go Block{..} = traverse_ go blockStmts
    go Skip{}    = return ()
    go Assignment{..} = do
      modify $ _2 %~ HS.insert (varName assignmentLhs)
      newReadVars <- HS.difference (getVariables assignmentRhs)
                     <$> gets (view _2)
      modify $ _1 %~ HS.union newReadVars
    go IfStmt{..} = do
      newReadVars <- HS.difference (getVariables ifStmtCondition)
                     <$> gets (view _2)
      modify $ _1 %~ HS.union newReadVars
      st <- get
      go ifStmtThen
      (rThen, wThen) <- get
      put st
      go ifStmtElse
      (rElse, wElse) <- get
      put (rThen <> rElse, wThen <> wElse)


getUpdatedVariables :: Members '[ Reader (HM.HashMap Id (Module Int))
                                , Reader AnnotationFile
                                ] r
                    => Thread Int
                    -> Sem r Ids
getUpdatedVariables = \case
  AB ab -> go $ abStmt ab
  MI mi@ModuleInstance{..} -> do
    (_, writtenVars) <-
      moduleInstanceReadsAndWrites
      <$> asks (HM.! moduleInstanceType)
      <*> getClocks moduleInstanceType
      <*> return mi
    return writtenVars
  where
    go = \case
      Block {..}      -> mfoldM go blockStmts
      Assignment {..} -> return . HS.singleton $ varName assignmentLhs
      IfStmt {..}     -> mfoldM go [ifStmtThen, ifStmtElse]
      Skip {..}       -> return mempty
