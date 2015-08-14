module Ditto.Syntax where

----------------------------------------------------------------------

type Name = String
type Cons = [(PName, Exp)]

data Stmt =
    SDef Name Exp Exp
  | SData PName Exp Cons
  | SDefn PName Exp [Clause]
  deriving (Show, Read, Eq)

newtype PName = PName { fromPName :: Name }
  deriving (Read, Eq)

instance Show PName where
  show (PName x) = "#" ++ x

data Exp =
    Type | Pi Name Exp Exp | Lam Name Exp Exp
  | Form PName [Exp] | Con PName [Exp]
  | Var Name | Exp :@: Exp | Red PName [Exp]
  deriving (Show, Read, Eq)

type Tel = [(Name, Exp)]
type Clause = ([Pat], Exp)

data Sigma =
    Def Name Exp Exp
  | DForm PName Tel
  | DCon PName Tel PName [Exp]
  | DRed PName [Clause] Tel Exp
  deriving (Show, Read, Eq)

data Pat = PVar Name | PCon Name [Name]
  deriving (Show, Read, Eq)

----------------------------------------------------------------------

varNames :: Tel -> [Exp]
varNames = map (Var . fst)

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
