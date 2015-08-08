module Ditto.Syntax where

----------------------------------------------------------------------

type Name = String
type Cons = [(Name, Exp)]

data Stmt = SDef Name Exp Exp
          | SData PName Exp Cons
  deriving (Show, Read, Eq)

newtype PName = PName { fromPName :: Name }
  deriving (Show, Read, Eq)

data Exp =
    Type | Pi Name Exp Exp | Lam Name Exp Exp
  | Form PName [Exp] | Con Name [Exp]
  | Var Name | Exp :@: Exp
  deriving (Show, Read, Eq)

type Tel = [(Name, Exp)]

data Sigma =
    Def Name Exp Exp
  | Virt Name Exp Exp
  | DForm PName Tel
  | DCon Name Tel PName [Exp]
  deriving (Show, Read, Eq)

data Pat = PVar Name | Inacc Exp | PCon Name [Pat]
  deriving (Show, Read, Eq)

----------------------------------------------------------------------

names :: Tel -> [Exp]
names = map (Var . fst)

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

conType :: Tel -> PName -> [Exp] -> Exp
conType _As _X _Is = pis _As (Form _X _Is)

----------------------------------------------------------------------
