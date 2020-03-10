-- {-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module Iodine.Language.PrologParser
  (
    Prolog(..)
  , parseProlog
  ) where

import           Control.Monad
import           Data.Bifunctor
import qualified Data.Text as T
import           Text.Megaparsec
import qualified Text.Megaparsec.Char as MPC
import qualified Text.Megaparsec.Char.Lexer as MPL
import qualified Text.PrettyPrint as PP

type Id = T.Text

data Prolog a =
    Number   Id a
  | Atom     Id a
  | String   Id a
  | Compound Id [Prolog a] a
  | List     [Prolog a] a
  | Tuple    [Prolog a] a
  deriving (Eq, Functor)

type Parser = Parsec SourcePos Id

toDoc :: Prolog a -> PP.Doc
toDoc = go
  where
    go (Number n _)      = t n
    go (Atom a _)        = t a
    go (String s _)      = PP.quotes $ t s
    go (Compound f as _) = PP.cat $ (t f PP.<> PP.lparen) : rest
      where
        rest =
          case as of
            [] -> [PP.rparen]
            _  -> let (is, l) = (init as, last as)
                  in fmap (\i -> PP.nest 2 $ go i <> PP.comma) is
                     ++ [PP.nest 2 $ go l <> PP.rparen]
          
    go (List as _)       = PP.brackets $ gos as
    go (Tuple as _)      = PP.parens $ gos as

    t = PP.text . T.unpack
    gos = PP.sep . PP.punctuate PP.comma . fmap go

instance Show (Prolog a) where
  show = PP.renderStyle sty . toDoc
    where
      sty = PP.style { PP.lineLength = 200 }

parseProlog :: FilePath -> Id -> Either String [Prolog ()]
parseProlog fp input =
  first myParseErrorPretty $
  runParser (whole $ many prologParser) fp input

prologParser :: Parser (Prolog ())
prologParser = just $
  (String <$> parseString <*> return ())
  <|> (List <$> list prologParser <*> return ())
  <|> (Tuple <$> parens prologParser <*> return ())
  <|> parseTerm
  <|> (Number <$> parseNumber <*> return ())

parseTerm :: Parser (Prolog ())
parseTerm = do 
  a <- parseVariable
  mas <- optional $ parens prologParser
  return $ case mas of
    Nothing -> Atom a ()
    Just as -> Compound a as ()

parseVariable :: Parser Id
parseVariable =
  just $ T.pack
  <$> ((:)
       <$> choice [MPC.letterChar, MPC.char '_']
       <*> many (choice [MPC.alphaNumChar, MPC.char '_']))

parseNumber :: Parser Id
parseNumber = just $ T.pack <$> some MPC.alphaNumChar

parseString :: Parser Id
parseString = just $ T.pack <$> between "\"" "\"" (many $ anySingleBut '\"')

list :: Parser a -> Parser [a]
list p = just $ between "[" "]" (commaSep p)

parens :: Parser a -> Parser [a]
parens p = just $ between "(" ")" (commaSep p)

commaSep :: Parser a -> Parser [a]
commaSep p = punctuate comma (just p)
  
whole :: Parser a -> Parser a
whole p = spaceConsumer *> p <* eof

comma :: Parser Id
comma = symbol ","

symbol :: Id -> Parser Id
symbol s = just $ MPL.symbol spaceConsumer s

just :: Parser a -> Parser a
just p = spaceConsumer *> p <* spaceConsumer

punctuate :: Parser sep -> Parser a -> Parser [a]
punctuate psep pa = do
  mh <- optional pa
  case mh of
    Nothing -> return []
    Just h  -> (:) h <$> many (psep *> pa)

spaceConsumer :: Parser ()
spaceConsumer = MPL.space (void MPC.spaceChar) lineCmnt blockCmnt
  where
    blockCmnt, lineCmnt :: Parser ()
    blockCmnt = MPL.skipBlockComment "/*" "*/"
    lineCmnt  = MPL.skipLineComment "%"

newtype SP = SP SourcePos
           deriving (Eq, Ord)

instance ShowErrorComponent SP where
  showErrorComponent (SP pos) = "parse error in file " ++ sourceName pos

myParseErrorPretty :: Stream s => ParseErrorBundle s e -> String
myParseErrorPretty (ParseErrorBundle errs posSt) =
  errorBundlePretty $
  ParseErrorBundle
  ((\(e,pos) -> mapParseError (const (SP pos)) e) <$> fst (attachSourcePos errorOffset errs posSt))
  posSt
