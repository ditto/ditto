module Ditto.Parse where
import Ditto.Syntax
import Text.Parsec (parse, try)
import Text.Parsec.String
import Text.Parsec.Char
import Text.Parsec.Combinator
import Control.Applicative ((<*), many, (<$>), (<*>), (<|>))
import Control.Monad

----------------------------------------------------------------------

parseE = parse (whitespace >> parseExp <* eof) "" . stripComments
parseP = parse (whitespace >> parseStmts <* eof) "" . stripComments

stripComments :: String -> String
stripComments = unlines . map (takeWhile (/= '#')) . lines

keyType = symbol "Type"
keyData = symbol "data"
keyDef = symbol "def"
keyWhere = symbol "where"
keyEnd = symbol "end"

keywords = choice
  [keyType, keyData, keyDef, keyWhere, keyEnd]

symAscribe = symbol ":"
symKind = symbol "::"
symChoice = symbol "|"
symInfer = symbol "*"
symHole = symbol "?"
symInacc = symbol "*"
symEq = symbol "="
symNeq = symbol "!="
symArr = symbol "->"
symSlash = symbol "/"

symLParen = symbol "("
symRParen = symbol ")"
symLBrace = symbol "{"
symRBrace = symbol "}"

----------------------------------------------------------------------

parseStmts :: Parser [Stmt]
parseStmts = many1 $ choice [
    parseDef
  , parseDefn
  , parseData
  ]

parseDef :: Parser Stmt
parseDef = try $ do
  keyDef
  x <- parseName
  optional $ symAscribe
  _A <- parseExp
  keyWhere
  a <- parseExp
  keyEnd
  return $ SDef x a _A

----------------------------------------------------------------------

parseDefn :: Parser Stmt
parseDefn = try $ do
  keyDef
  x <- parsePName
  optional $ symAscribe
  _A <- parseExp
  keyWhere
  cs <- many1 parseClause
  keyEnd
  return $ SDefn x _A cs

parseClause :: Parser Clause
parseClause = try $ do
  symChoice
  ps <- many parsePattern
  a <- parseRHS
  return (ps , a)

parseRHS :: Parser RHS
parseRHS = choice
  [ try $ Prog <$> (symEq >> parseExp)
  , try $ Caseless <$> (symNeq >> parseName)
  ]

----------------------------------------------------------------------

parsePattern :: Parser (Icit, Pat)
parsePattern = choice
  [ parseImplPat parsePVar
  , parseExplPat parsePVar
  , parseImplPat parsePInacc
  , parseExplPat parsePInacc
  , parseImplPat parsePCon
  , parseExplPat (parens parsePCon)
  ]

parseImplPat :: Parser Pat -> Parser (Icit, Pat)
parseImplPat p = (Impl,) <$> try (braces p)

parseExplPat :: Parser Pat -> Parser (Icit, Pat)
parseExplPat p = (Expl,) <$> try p

parsePCon :: Parser Pat
parsePCon = try $ do
  x <- parsePName
  xs <- many parsePattern
  return $ PCon x xs

parsePVar :: Parser Pat
parsePVar = try $ PVar <$> parseName

parsePInacc :: Parser Pat
parsePInacc = try $ do
  symInacc
  return $ Inacc Nothing

----------------------------------------------------------------------

parseData :: Parser Stmt
parseData = try $ do
  keyData
  x <- parsePName
  _As <- parseParams <|> (optional symAscribe >> return [])
  _B <- pis _As <$> parseExp
  keyWhere
  cons <- paramCons _As . concat <$> many parseCon
  keyEnd
  return $ SData x _B cons

parseParams :: Parser Tel
parseParams = try $ do
  _As <- parseTel
  symKind
  return _As

parseCon :: Parser Cons
parseCon = try $ do
  symChoice
  xs <- slashSep parsePName
  optional $ symAscribe
  _A <- parseExp
  return (map (\x -> (x, _A)) xs)

----------------------------------------------------------------------

parseExp :: Parser Exp
parseExp = choice [
    parsePi
  , parseLam
  , parseApps
  ]

parseApps :: Parser Exp
parseApps = apps <$> parseAtom <*> many parseApp

parseApp :: Parser (Icit, Exp)
parseApp = parseImplApp <|> parseExplApp

parseImplApp :: Parser (Icit, Exp)
parseImplApp = (Impl,) <$> try (braces parseExp)

parseExplApp :: Parser (Icit, Exp)
parseExplApp = (Expl,) <$> parseAtom

parseAtom :: Parser Exp
parseAtom = choice [
    parens parseExp
  , parseType
  , parseInfer
  , parseHole
  , parseVar
  ]

----------------------------------------------------------------------

parseType :: Parser Exp
parseType = try $ keyType >> return Type

parseInfer :: Parser Exp
parseInfer = try $ symInfer >> return (Infer MInfer)

parseHole :: Parser Exp
parseHole = try $ do
    symHole
    nm <- optionMaybe parseIdent
    return (Infer $ MHole nm)

parseVar :: Parser Exp
parseVar = try $ Var <$> parseName

parsePName :: Parser PName
parsePName = PName <$> parseIdent

parseName :: Parser Name
parseName = s2n <$> parseIdent

parseIdent :: Parser String
parseIdent = try $ do
  notFollowedBy keywords
  lexeme ((:) <$> firstChar <*> many nextChar)
  where
  firstChar = letter
  nextChar = choice [alphaNum, char '\'']

----------------------------------------------------------------------

parsePi :: Parser Exp
parsePi = try $ do
  _As <- parseTel
  symAscribe
  _A <- parseExp
  return $ pis _As _A

parseLam :: Parser Exp
parseLam = try $ do
  _As <- parseTel
  symArr
  b <- parseExp
  return $ lams _As b

----------------------------------------------------------------------

parseTel :: Parser Tel
parseTel = concat <$> many1 (parseImplAnnot <|> parseExplAnnot)

parseImplAnnot :: Parser Tel
parseImplAnnot = try $ braces $ do
  xs <- many1 parseName
  symAscribe
  a <- parseExp
  return $ map (\ x -> (Impl, x , a)) xs

parseExplAnnot :: Parser Tel
parseExplAnnot = try $ parens $ do
  xs <- many1 parseName
  symAscribe
  a <- parseExp
  return $ map (\ x -> (Expl, x , a)) xs

----------------------------------------------------------------------

slashSep :: Parser a -> Parser [a]
slashSep p = p `sepBy1` symSlash

parens :: Parser a -> Parser a
parens = between symLParen symRParen

braces :: Parser a -> Parser a
braces = between symLBrace symRBrace

symbol :: String -> Parser String
symbol s = lexeme $ string s

lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace

whitespace :: Parser ()
whitespace = void $ many $ oneOf " \n\t"

----------------------------------------------------------------------
