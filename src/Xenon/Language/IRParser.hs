{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Xenon.Language.IRParser (parse) where

import           Xenon.Language.IR
import           Xenon.Types

import           Control.Effect.Error
import           Data.Char (isLetter, isDigit)
import           Data.Foldable
import           Data.Functor
import qualified Data.HashMap.Strict as HM
import           Data.Hashable
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Text.Megaparsec ((<|>))
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MPC
import qualified Text.Megaparsec.Char.Lexer as MPL

type Parser = MP.Parsec MP.SourcePos String
type ParsedIR = L (Module ())

parse :: Has (Error XenonException) sig m => (FilePath, String) -> m ParsedIR
parse (fp, s) = parseWith (many parseModule)
  where
    parseWith p =
      case MP.runParser (whole p) fp s of
        Right e     -> return e
        Left bundle -> throwError (IE IRParser (myParseErrorPretty bundle))

--------------------------------------------------------------------------------
-- | IR Parser
--------------------------------------------------------------------------------

parseModule :: Parser (Module ())
parseModule =
  parseTerm "module" $
  Module
  <$> identifier
  <*> (comma *> list parsePort)
  <*> (comma *> list parseVariable)
  <*> (comma *> list parseVarInit)
  <*> (comma *> parseVerilogFunctions)
  <*> (comma *> list parseStmt)
  <*> (comma *> list parseAlwaysBlock)
  <*> (comma *> list parseModuleInstance)
  <*> parseData

parsePort :: Parser Port
parsePort =
  parseTerm "input"  (Input   <$> parseVariable) <|>
  parseTerm "output" (Output  <$> parseVariable)

parseVariable :: Parser Variable
parseVariable =
  parseTerm "wire"     (Wire     <$> identifier) <|>
  parseTerm "register" (Register <$> identifier)

parseExpr :: Parser (Expr ())
parseExpr =
  parseConstantExpr <|>
  parseVarExpr <|>
  parseVFCallExpr <|>
  parseTerm "uf" (UF <$> parseUFOp <*> (comma *> list parseExpr) <*> parseData) <|>
  parseTerm "ite_expr" (IfExpr
                        <$> parseExpr
                        <*> (comma *> parseExpr)
                        <*> (comma *> parseExpr)
                        <*> parseData) <|>
  parseTerm "str" (Str <$> identifier <*> parseData) <|>
  parseTerm "select" (Select
                      <$> parseExpr
                      <*> (comma *> list parseExpr)
                      <*> parseData)

parseUFOp :: Parser UFOp
parseUFOp = do
  f <- identifier
  return $
    case f of
      "abs"            -> UF_abs
      "and"            -> UF_and
      "negate"         -> UF_negate
      "negative"       -> UF_negative
      "not"            -> UF_not
      "add"            -> UF_add
      "or"             -> UF_or
      "arith_rs"       -> UF_arith_rs
      "bitwise_and"    -> UF_bitwise_and
      "bitwise_or"     -> UF_bitwise_or
      "case_eq"        -> UF_case_eq
      "case_neq"       -> UF_case_neq
      "div"            -> UF_div
      "exp"            -> UF_exp
      "ge"             -> UF_ge
      "gt"             -> UF_gt
      "le"             -> UF_le
      "logic_eq"       -> UF_logic_eq
      "logic_neq"      -> UF_logic_neq
      "lt"             -> UF_lt
      "mod"            -> UF_mod
      "mul"            -> UF_mul
      "nand"           -> UF_nand
      "nor"            -> UF_nor
      "shl"            -> UF_shl
      "shr"            -> UF_shr
      "sub"            -> UF_sub
      "xnor"           -> UF_xnor
      "xor"            -> UF_xor
      "concat"         -> UF_concat
      "write_to_index" -> UF_write_to_index
      _                -> error $ "parseUFOp failed: " ++ T.unpack f

parseVFCallExpr :: Parser (Expr ())
parseVFCallExpr =
  parseTerm "vfcall" (VFCall <$>
                      identifier <*>
                      (comma *> list parseExpr) <*>
                      parseData)

parseConstantExpr :: Parser (Expr ())
parseConstantExpr =
  parseTerm "const" (Constant <$> constVar <*> parseData)
  where
    constVar :: Parser Id
    constVar = T.pack <$> MP.many MPC.alphaNumChar

parseVarExpr :: Parser (Expr ())
parseVarExpr =
  parseTerm "var" (Variable <$> identifier <*> (comma *> identifier) <*> parseData)

parseStmt :: Parser (Stmt ())
parseStmt =
  parseTerm "block" (Block <$> list parseStmt <*> parseData) <|>
  parseAsn "b_asn" Blocking <|>
  parseAsn "nb_asn" NonBlocking <|>
  parseAsn "asn" Continuous <|>
  parseTerm "ite_stmt" (IfStmt
                        <$> parseExpr
                        <*> (comma *> parseStmt)
                        <*> (comma *> parseStmt)
                        <*> parseData) <|>
  (rWord "skip" $> Skip ())
  where
    parseAsn k t = parseTerm k $
                   Assignment t
                   <$> parseExpr
                   <*> (comma *> parseExpr)
                   <*> parseData

parseModuleInstance :: Parser (ModuleInstance ())
parseModuleInstance =
  parseTerm "mod_inst" $
  ModuleInstance
  <$> identifier
  <*> (comma *> identifier)
  <*> (comma *> parseMap identifier parseExpr)
  <*> parseData


parseEvent :: Parser (Event ())
parseEvent =
  parseTerm "posedge" (PosEdge <$> parseExpr) <|>
  parseTerm "negedge" (NegEdge <$> parseExpr) <|>
  (rWord "star" $> Star)

parseAlwaysBlock :: Parser (AlwaysBlock ())
parseAlwaysBlock =
  parseTerm "always" (AlwaysBlock
                     <$> parseEvent
                     <*> (comma *> parseStmt)
                     <*> return ())

parseVarInit :: Parser (Id, Expr ())
parseVarInit = parens $ (,) <$> identifier <*> (comma *> parseExpr)

parseVerilogFunctions :: Parser (HM.HashMap Id (VerilogFunction ()))
parseVerilogFunctions =
  foldl' (\m vf -> HM.insert (verilogFunctionName vf) vf m) mempty
  <$> list parseVerilogFunction

parseVerilogFunction :: Parser (VerilogFunction ())
parseVerilogFunction =
  parseTerm "function" $ do
    fn <- identifier
    ps <- comma *> list identifier
    e <- comma *> parseExpr
    return $ VerilogFunction fn ps e ()

parseData :: Parser ()
parseData = return ()

--------------------------------------------------------------------------------
-- | Tokenisers and Whitespace
--------------------------------------------------------------------------------

parseTerm :: String -> Parser a -> Parser a
parseTerm t p = rWord t *> parens p

parseMap :: (Eq k, Hashable k)
         => Parser k -> Parser v -> Parser (HM.HashMap k v)
parseMap kp vp = HM.fromList . toList <$> list ( parens ((,) <$> kp <*> (comma *> vp)))

-- | Top-level parsers (should consume all input)
whole :: Parser a -> Parser a
whole p = spaceConsumer *> p <* MP.eof

spaceConsumer :: Parser ()
spaceConsumer = void $ MP.many MPC.spaceChar

-- | `symbol s` parses just the string s (and trailing whitespace)
symbol :: String -> Parser Id
symbol s = T.pack <$> MPL.symbol spaceConsumer s

comma :: Parser Id
comma = symbol ","

-- lparen, rparen :: Parser Id
-- lparen = symbol "("
-- rparen = symbol ")"

-- | 'parens' parses something between parenthesis.
parens :: Parser a -> Parser a
parens = betweenS "(" ")"

list :: Parser a -> Parser (L a)
list p = betweenS "[" "]" (sepBy comma p)

betweenS :: String -> String -> Parser a -> Parser a
betweenS l r = MP.between (symbol l) (symbol r)

-- | `lexeme p` consume whitespace after running p
lexeme :: Parser a -> Parser a
lexeme = MPL.lexeme spaceConsumer

-- | `rWord`
rWord   :: String -> Parser Id
rWord w = (T.pack <$> MPC.string w) <* MP.notFollowedBy MPC.alphaNumChar <* spaceConsumer

many :: Parser a -> Parser (L a)
many p = go id
  where
    go f = do
      r <- MP.optional p
      case r of
        Nothing -> return (f SQ.empty)
        Just  x -> go (f . (x SQ.<|))
{-# INLINE many #-}

sepBy :: Parser sep -> Parser a -> Parser (L a)
sepBy sep p = do
  r <- MP.optional p
  case r of
    Nothing -> return SQ.empty
    Just  x -> (x SQ.<|) <$> many (sep >> p)
{-# INLINE sepBy #-}

keywords :: [Id]
keywords =
  [ "register", "wire", "input", "output", "posedge", "negedge", "star", "always", "module" -- module
  , "const", "var", "uf", "ite_expr", "str", "select"                 -- expr
  , "block", "b_asn", "nb_asn", "asn", "ite_stmt", "skip", "mod_inst" -- stmt
  ]

identifier :: Parser Id
identifier = lexeme (p >>= check)
  where
    p :: Parser Id
    p = T.cons <$> (MPC.letterChar <|> MPC.char '_') <*> (T.pack <$> MP.many nonFirstChar)

    nonFirstChar :: Parser Char
    nonFirstChar = MP.satisfy (\a -> isDigit a || isLetter a || a == '_')

    check x = if x `elem` keywords
              then fail $ "keyword " ++ show x ++ " cannot be an identifier"
              else return x

--------------------------------------------------------------------------------
-- | Error handling
--------------------------------------------------------------------------------

newtype SP = SP MP.SourcePos
           deriving (Eq, Ord)

instance MP.ShowErrorComponent SP where
  showErrorComponent (SP pos) = "parse error in file " ++ MP.sourceName pos

myParseErrorPretty :: MP.Stream s => MP.ParseErrorBundle s e -> String
myParseErrorPretty (MP.ParseErrorBundle errs posSt) =
  MP.errorBundlePretty $
  MP.ParseErrorBundle
  ((\(e,pos) -> MP.mapParseError (const (SP pos)) e) <$> fst (MP.attachSourcePos MP.errorOffset errs posSt))
  posSt
