module Ditto.Parse where
import Ditto.Syntax
import Text.Parsec (parse, try)
import Text.Parsec.String
import Text.Parsec.Char
import Text.Parsec.Combinator
import Control.Applicative
import Control.Monad

----------------------------------------------------------------------

parseE = parse (whitespace >> parseExp <* eof) ""
parseP = parse (whitespace >> parseStmts <* eof) ""

keywords = choice $ map symbol ["Type", "data", "def", "where", "end"]

----------------------------------------------------------------------

parseStmts :: Parser [Stmt]
parseStmts = many $ choice [
    parseDef
  ]

parseDef :: Parser Stmt
parseDef = try $ do
  symbol "def"
  x <- parseName
  symbol ":"
  _A <- parseExp
  symbol "where"
  a <- parseExp
  symbol "end"
  return $ SDef x a _A

----------------------------------------------------------------------

parseExp :: Parser Exp
parseExp = choice [
    parsePi
  , parseLam
  , parseApps
  ]

parseApps :: Parser Exp
parseApps = apps <$> many1 parseAtom

parseAtom :: Parser Exp
parseAtom = choice [
    parens parseExp
  , parseType
  , parseVar
  ]

----------------------------------------------------------------------

parseType :: Parser Exp
parseType = try $ symbol "Type" >> return Type

parseVar :: Parser Exp
parseVar = try $ EVar <$> parseName

parseName :: Parser Name
parseName = try $ do
  notFollowedBy keywords
  lexeme ((:) <$> firstChar <*> many nextChar)
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





