module Ditto.Syntax where

----------------------------------------------------------------------

type Name = String

data Exp = EVar Name | Type | Pi Name Exp Exp | Lam Name Exp Exp | Exp :@: Exp
  deriving (Show, Read, Eq)

type Tel = [(Name, Exp)]

data Sigma =
    Def Name Exp Exp
  | Virt Name Exp Exp
  | Data
    { dname :: Name
    , dpars :: Tel
    , dixs  :: Tel
    , dcons :: [ConDecl]
    }

data ConDecl = ConDecl
  { cname :: Name
  , cargs :: Tel
  , cixs  :: [Exp]
  }

data Pat = PVar Name | Inacc Exp | Con Name [Pat]
  deriving (Show, Read, Eq)

----------------------------------------------------------------------

pis :: Tel -> Exp -> Exp
pis = flip $ foldr (\ (x , _A) _B -> Pi x _A _B)

lams :: Tel -> Exp -> Exp
lams = flip $ foldr (\ (x , _A) _B -> Lam x _A _B)

apps :: [Exp] -> Exp
apps (x:xs) = foldl (:@:) x xs
apps [] = error "Application must have at least one argument"

----------------------------------------------------------------------

