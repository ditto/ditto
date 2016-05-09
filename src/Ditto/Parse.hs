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
parseP = parse (whitespace >> parseProg <* eof) "" . stripComments

stripComments :: String -> String
stripComments = unlines . map (takeWhile (/= '#')) . lines

keyType = symbol "Type"
keyData = symbol "data"
keyMutual = symbol "mutual"
keyDef = symbol "def"
keyWhere = symbol "where"
keyEnd = symbol "end"

keywords = choice
  [keyType, keyData, keyDef, keyWhere, keyEnd]

symAscribe = symbol ":"
symKind = symbol "::"
symChoice = symbol "|"
symInfer = symbol "*"
strHole = "?"
symHole = symbol strHole
symInacc = symbol "*"
symEq = symbol "="
symNeq = symbol "!="
symAt = symbol "@"
symArr = symbol "->"
symComma = symbol ","

symLParen = symbol "("
symRParen = symbol ")"
symLBrace = symbol "{"
symRBrace = symbol "}"

----------------------------------------------------------------------

parseProg :: Parser Prog
parseProg = many1 $ (Right <$> parseMutual) <|> (Left <$> parseStmt)

parseStmt :: Parser Stmt
parseStmt = choice [
    parseDef
  , parseDefn
  , parseData
  ]

parseMutual :: Parser [Stmt]
parseMutual = try $ do
  keyMutual
  xs <- many1 parseStmt
  keyEnd
  return xs

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
  [ try $ MapsTo <$> (symEq >> parseExp)
  , try $ Caseless <$> (symNeq >> parseName)
  , try $ Split <$> (symAt >> parseName)
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
parsePVar = try $ PVar <$> parseAccName

parsePInacc :: Parser Pat
parsePInacc = try $ do
  symInacc
  return $ PInacc Nothing

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
  xs <- commaSep parsePName
  optional symAscribe
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
parseHole = parseNamedHole <|> parseAnonHole

parseNamedHole :: Parser Exp
parseNamedHole = try $ do
  string strHole
  nm <- parseIdent
  return . Infer . MHole . Just $ nm

parseAnonHole :: Parser Exp
parseAnonHole = try $ do
  symHole
  return . Infer . MHole $ Nothing

parseVar :: Parser Exp
parseVar = try $ Var <$> parseName

parsePName :: Parser PName
parsePName = PName <$> parseIdent

parseName :: Parser Name
parseName = parseAccName <|> parseInaccName

parseAccName :: Parser Name
parseAccName = s2n Acc <$> parseIdent

parseInaccName :: Parser Name
parseInaccName = try $ do
  symInacc
  return (s2n Inacc "x")

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
  xs <- commaSep parseName
  optional symAscribe
  a <- parseExp
  return $ map (\ x -> (Impl, x , a)) xs

parseExplAnnot :: Parser Tel
parseExplAnnot = try $ parens $ do
  xs <- commaSep parseName
  optional symAscribe
  a <- parseExp
  return $ map (\ x -> (Expl, x , a)) xs

----------------------------------------------------------------------

commaSep :: Parser a -> Parser [a]
commaSep p = p `sepBy1` symComma

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
