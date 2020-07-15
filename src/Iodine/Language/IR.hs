{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE StrictData          #-}

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
  , defaultDocConfig
  , colorId
  , prettyShow
  , prettyShowWithConfig
  , Doc(..)
  )
where

import           Iodine.Language.Annotation
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.State.Strict
import           Control.Effect.Reader
import           Control.Lens hiding (op)
import           Data.Bifunctor
import           Data.Foldable
import           Data.Functor (void)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Hashable
import           Data.Maybe
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           GHC.Generics hiding (moduleName)
import qualified Text.PrettyPrint as PP

data Variable =
    Wire     { variableName :: Id }
  | Register { variableName :: Id }
  deriving (Eq, Show, Read)

data Port =
    Input  { portVariable :: Variable }
  | Output { portVariable :: Variable }
  deriving (Eq, Show, Read)

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
  deriving (Eq, Generic, Functor, Foldable, Traversable, Show, Read)

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
  deriving (Eq, Show, Read)
{- HLINT ignore UFOp -}

data AssignmentType = Blocking | NonBlocking | Continuous
                    deriving (Generic, Eq, Show, Read)

data ModuleInstance a =
  ModuleInstance { moduleInstanceType  :: Id
                 , moduleInstanceName  :: Id
                 , moduleInstancePorts :: HM.HashMap Id (Expr a)
                 , moduleInstanceData  :: a
                 }
  deriving (Generic, Functor, Foldable, Traversable, Show, Eq, Read)

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
  deriving (Generic, Functor, Foldable, Traversable, Show, Eq, Read)

data Event a =
    PosEdge { eventExpr :: Expr a }
  | NegEdge { eventExpr :: Expr a }
  | Star
  deriving (Generic, Functor, Foldable, Traversable, Eq, Show, Read)

data AlwaysBlock a =
    AlwaysBlock { abEvent :: Event a
                , abStmt  :: Stmt a
                , abData  :: a
                }
  deriving (Generic, Functor, Foldable, Traversable, Show, Eq, Read)

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
  deriving (Generic, Functor, Foldable, Traversable, Show, Eq, Read)

-- | An always block or a module instance
data Thread a = AB (AlwaysBlock a)
              | MI (ModuleInstance a)
  deriving (Eq, Show, Read)

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
  showIndex    :: a -> String

instance ShowIndex () where
  showIndex () = ""

instance ShowIndex Int where
  showIndex n = " #" ++ show n

docIndex :: ShowIndex a => a -> PP.Doc
docIndex = PP.text . showIndex

data DocColor = Red | Blue | Green deriving Eq

minDocColor :: DocColor
minDocColor = minimum [Red, Blue, Green]

instance Ord DocColor where
  compare c1 c2 =
    if   c1 == c2
    then EQ
    else case (c1, c2) of
      (Red, _)    -> LT
      (_,  Green) -> LT
      (Green, _ ) -> GT
      (Blue, Red) -> GT
      _           -> error "unreachable"

colorId :: DocColor -> Id -> String
colorId c v = "\x1b[1m" <> colorPrefix <> s <> "\x1b[0m"
  where
    colorPrefix =
      case c of
        Red   -> "\x1b[31m"
        Blue  -> "\x1b[34m"
        Green -> "\x1b[32m"
    s = T.unpack v

data DocConfig a = DocConfig
  { varColorMap     :: a -> Id -> Maybe DocColor
  , currentDocIndex :: Maybe a
  }

defaultDocConfig :: DocConfig a
defaultDocConfig = DocConfig (\_ _ -> Nothing) Nothing

class DocSimple d where
  docSimple :: d -> PP.Doc

class Doc m where
  doc :: ShowIndex a => DocConfig a -> m a -> PP.Doc

sep :: PP.Doc
sep = PP.comma

nest :: PP.Doc -> PP.Doc
nest = PP.nest 2

vcatSimple :: DocSimple d => L d -> PP.Doc
vcatSimple = PP.vcat . fmap docSimple . toList

vcat :: (ShowIndex a, Doc m) => DocConfig a -> L (m a) -> PP.Doc
vcat c = PP.vcat . fmap (doc c) . toList

id2Doc :: Id -> PP.Doc
id2Doc = PP.text . T.unpack

instance DocSimple Variable where
  docSimple (Wire v)     = PP.text "wire" PP.<+> id2Doc v PP.<> PP.semi
  docSimple (Register v) = PP.text "reg " PP.<+> id2Doc v PP.<> PP.semi

instance DocSimple Port where
  docSimple (Input p)  = PP.text "input " PP.<+> id2Doc (variableName p) PP.<> PP.semi
  docSimple (Output p) = PP.text "output" PP.<+> id2Doc (variableName p) PP.<> PP.semi

instance DocSimple UFOp where
  docSimple = PP.text . \case
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

instance Doc Expr where
  doc _ (Constant c _)   = id2Doc c
  doc DocConfig{..} (Variable v _ a) = str PP.<> docIndex a
    where str = case currentDocIndex >>= (`varColorMap` v) of
                  Nothing -> id2Doc v
                  Just dc -> PP.text $ colorId dc v

  doc cfg (UF n es _) =
    case n of
      UF_add            -> commonB "+"
      UF_and            -> commonB "&&"
      UF_negate         -> commonB "¬"
      UF_negative       -> commonB "-"
      UF_not            -> commonB "!"
      UF_or             -> commonB "||"
      UF_arith_rs       -> commonB ">>"
      UF_bitwise_and    -> commonB "&"
      UF_bitwise_or     -> commonB "|"
      UF_case_eq        -> commonB "=="
      UF_case_neq       -> commonB "!="
      UF_div            -> commonB "/"
      UF_ge             -> commonB ">="
      UF_gt             -> commonB ">"
      UF_le             -> commonB "<="
      UF_logic_eq       -> commonB "=="
      UF_logic_neq      -> commonB "!="
      UF_lt             -> commonB "<"
      UF_mod            -> commonB "%"
      UF_mul            -> commonB "*"
      UF_nand           -> commonB "!&&"
      UF_nor            -> commonB "!||"
      UF_shl            -> commonB "<<"
      UF_shr            -> commonB ">>"
      UF_sub            -> commonB "-"
      UF_xnor           -> commonB "!^"
      UF_xor            -> commonB "^"
      _ -> common
    where
      d = doc cfg
      commonB bop = commonB2 bop True es
      commonB2 bop isTop = withParens .
        \case
          SQ.Empty                     -> PP.empty
          e SQ.:<| SQ.Empty            -> PP.text bop PP.<> PP.parens (d e)
          e1 SQ.:<| e2 SQ.:<| SQ.Empty -> d e1 PP.<+> PP.text bop PP.<+> d e2
          e SQ.:<| rest                -> d e PP.<+> PP.text bop PP.<+> PP.parens (commonB2 bop False rest)
        where
          withParens = if isTop then id else PP.parens
      common = docSimple n PP.<> PP.parens args
      args = PP.sep $ PP.punctuate sep (d <$> toList es)
  doc cfg (IfExpr c t e _) = PP.parens $ PP.hsep [doc cfg c, PP.text "?", doc cfg t, PP.colon, doc cfg e]
  doc _   (Str s _)        = PP.quotes $ id2Doc s
  doc cfg (Select v is _)  = doc cfg v PP.<> PP.brackets (docList cfg is)
    where docList c l = PP.hsep $ PP.punctuate sep (doc c <$> toList l)


instance Doc Event where
  doc c (PosEdge e) = PP.text "@(posedge " PP.<> doc c e PP.<> PP.rparen
  doc c (NegEdge e) = PP.text "@(negedge " PP.<> doc c e PP.<> PP.rparen
  doc _ Star        = PP.text "@(*)"

instance Doc Stmt where
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
    PP.cat $
    [ PP.text "if" PP.<+> PP.parens (doc cfg c) PP.<+> PP.lbrace
    , nest $ doc cfg t
    ] ++
    concat
    [ [ PP.rbrace PP.<+> PP.text "else if" PP.<+> PP.parens (doc cfg c2) PP.<+> PP.lbrace
      , nest $ doc cfg t2
      ]
    | (c2, t2) <- elseIfs
    ] ++
    [ PP.rbrace PP.<+> PP.text "else" PP.<+> PP.lbrace
    , nest $ doc cfg lastStmt
    , PP.rbrace
    ]
    where
      go IfStmt{..} = (Just ifStmtCondition, ifStmtThen) : go ifStmtElse
      go s          = [(Nothing, s)]
      rest = go e
      (elseIfs, lastStmt) = (first fromJust <$> init rest, snd $ last rest)
  doc _ (Skip _) = PP.text "skip" PP.<> PP.semi

instance Doc ModuleInstance where
  doc c (ModuleInstance t n ps a) =
    id2Doc t PP.<+> id2Doc n PP.<> PP.parens (PP.hsep $ PP.punctuate sep args) PP.<> docIndex a
    where
      args = docArgs ps
      docArgs =
        HM.foldlWithKey'
        (\acc v e-> (id2Doc v PP.<+> PP.equals PP.<+> doc fixedC e) : acc)
        []
      fixedC = c { currentDocIndex = Just a }

instance Doc AlwaysBlock where
  doc c (AlwaysBlock e s a) =
    PP.sep [ PP.text "always"
             PP.<> PP.text (showIndex a)
             PP.<+> doc fixedC e
           , doc fixedC s
           ]
    where fixedC = c { currentDocIndex = Just a }

instance Doc Module where
  doc (c :: DocConfig a) Module{..} =
    PP.vcat [ PP.text "module" PP.<> docIndex moduleData PP.<+> id2Doc moduleName PP.<> PP.parens args PP.<> PP.semi
            , PP.nest 2 contents
            , PP.text "endmodule"
            ]
    where
      contents =
        vcatNL [ vcatSimple ports
               , vcatSimple variables
               , vcatNS cNoIndex gateStmts
               , vcatNS cMIIndex moduleInstances
               , vcatNS cNoIndex alwaysBlocks
               ]
      args =
        PP.hsep $
        PP.punctuate sep (id2Doc . variableName . portVariable <$> toList ports)

      vcatNS :: Doc d2 => DocConfig a -> L (d2 a) -> PP.Doc
      vcatNS c2 = vcatNL . fmap (doc c2) . toList

      vcatNL :: [PP.Doc] -> PP.Doc
      vcatNL = PP.vcat . go . filter (not . PP.isEmpty)
        where
          go []     = []
          go [a]    = [a]
          go (a:as) = a : PP.text "" : go as

      cNoIndex = c{currentDocIndex = Nothing}
      cMIIndex = c{varColorMap =
                      let getColor [] = Just minDocColor
                          getColor cs = Just $ maximum cs
                          abIndices   = getData <$> toList alwaysBlocks
                      in \_ v -> getColor $ catMaybes $ (\a -> varColorMap c a v) <$> abIndices
                  }

iodineRender :: PP.Doc -> String
iodineRender = PP.renderStyle sty
  where
    sty = PP.style { PP.lineLength = 200 }

prettyShow :: (ShowIndex a, Doc d) => d a -> String
prettyShow = prettyShowWithConfig defaultDocConfig

prettyShowWithConfig :: (ShowIndex a, Doc d) => DocConfig a -> d a -> String
prettyShowWithConfig cfg = iodineRender . doc cfg

instance Hashable a => Hashable (Expr a) where
  hashWithSalt n (Variable v m a) = hashWithSalt n (v,m,a)
  hashWithSalt _ _                = notSupported

instance Hashable a => Hashable (Event a) where
  hashWithSalt n (PosEdge e) = hashWithSalt n (1::Int, e)
  hashWithSalt n (NegEdge e) = hashWithSalt n (2::Int, e)
  hashWithSalt n Star        = hashWithSalt n (3::Int)

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

type Ids2 = (Ids,Ids)
-- | given a module, module's clocks and an instance of it, returns the
-- variables that are read and written by the instance.
moduleInstanceReadsAndWrites :: Module a -> Ids -> ModuleInstance a -> (Ids, Ids)
moduleInstanceReadsAndWrites m mClks mi = run $ execState (mempty, mempty) $ do
  for_ miInputs $ \inputPort ->
    for_ (getVariables $ moduleInstancePorts mi HM.! inputPort) $ \v ->
    modify @Ids2 (_1 %~ HS.insert v)
  for_ miOutputs $ \outputPort -> do
    let portExpr    = moduleInstancePorts mi HM.! outputPort
        updatedVars = getUpdatedVars portExpr
        readVars    = getVariables portExpr `HS.difference` updatedVars
    for_ readVars    $ \v -> modify @Ids2 (_1 %~ HS.insert v)
    for_ updatedVars $ \v -> modify @Ids2 (_2 %~ HS.insert v)
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
    go :: Has (State (Ids, Ids)) sig m => Stmt a -> m ()
    go Block{..} = traverse_ go blockStmts
    go Skip{}    = return ()
    go Assignment{..} = do
      modify @Ids2 $ _2 %~ HS.insert (varName assignmentLhs)
      newReadVars <- HS.difference (getVariables assignmentRhs)
                     <$> gets @Ids2 (view _2)
      modify @Ids2 $ _1 %~ HS.union newReadVars
    go IfStmt{..} = do
      newReadVars <- HS.difference (getVariables ifStmtCondition)
                     <$> gets @Ids2 (view _2)
      modify @Ids2 $ _1 %~ HS.union newReadVars
      st <- get @Ids2
      go ifStmtThen
      (rThen, wThen) <- get @Ids2
      put st
      go ifStmtElse
      (rElse, wElse) <- get
      put @Ids2 (rThen <> rElse, wThen <> wElse)


getUpdatedVariables :: ( Has (Reader (HM.HashMap Id (Module Int))) sig m
                       , Has (Reader AnnotationFile) sig m
                       )
                    => Thread Int
                    -> m Ids
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
