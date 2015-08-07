module Ditto.Parse where
import Ditto.Syntax
import Text.Parsec (parse, try)
import Text.Parsec.String
import Text.Parsec.Char
import Text.Parsec.Combinator
import Control.Applicative
import Control.Monad

----------------------------------------------------------------------

keywords = ["Type", "data", "def", "end"]

----------------------------------------------------------------------

parseExp :: Parser Exp
parseExp = choice [
    parsePi
  , parseLam
  , parseAtom
  ]

parseAtom :: Parser Exp
parseAtom = choice [
    parens parseExp
  , parseType
  , parseVar
  ]

----------------------------------------------------------------------

parseType :: Parser Exp
parseType = try $ symbol "type" >> return Type

parseVar :: Parser Exp
parseVar = try $ EVar <$> parseName

parseName :: Parser Name
parseName = try $ lexeme ((:) <$> firstChar <*> many nextChar)
  where
  firstChar = letter
  nextChar = alphaNum

----------------------------------------------------------------------

parsePi :: Parser Exp
parsePi = try $ do
  _As <- parseTel
  symbol ":"
  _A <- parseExp
  return $ pis _As _A

parseLam :: Parser Exp
parseLam = try $ do
  _As <- parseTel
  symbol "->"
  b <- parseExp
  return $ lams _As b

----------------------------------------------------------------------

parseTel :: Parser Tel
parseTel = many1 (parens parseAnnot)

parseAnnot :: Parser (Name, Exp)
parseAnnot = do
  x <- parseName
  symbol ":"
  a <- parseExp
  return (x , a)

----------------------------------------------------------------------

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

symbol :: String -> Parser String
symbol s = lexeme $ string s

lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace

whitespace :: Parser ()
whitespace = void $ many $ oneOf " \n\t"

----------------------------------------------------------------------





