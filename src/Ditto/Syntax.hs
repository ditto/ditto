module Ditto.Syntax where

----------------------------------------------------------------------

type Name = String

data Exp =
    Type | Pi Name Exp Exp | Lam Name Exp Exp
  | Form Name [Exp] | Con Name [Exp]
  | EVar Name | Exp :@: Exp
  deriving (Show, Read, Eq)

type Tel = [(Name, Exp)]

data Sigma =
    Def Name Exp Exp
  | Virt Name Exp Exp
  | DForm Name Tel
  | DCon Name Tel Name [Exp]
  deriving (Show, Read, Eq)

data Pat = PVar Name | Inacc Exp | PCon Name [Pat]
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

formType :: Tel -> Exp
formType _Is = pis _Is Type

conType :: Tel -> Name -> [Exp] -> Exp
conType _As _X _Is = pis _As (apps (EVar _X : _Is))

----------------------------------------------------------------------

