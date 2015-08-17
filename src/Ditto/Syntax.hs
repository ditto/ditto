module Ditto.Syntax where

----------------------------------------------------------------------

data Name = Name String (Maybe Integer)
  deriving (Read, Eq)

instance Show Name where
  show (Name x Nothing) = show x
  show (Name x (Just n)) = show x ++ "$" ++ show n

s2n :: String -> Name
s2n x = Name x Nothing

uniqName :: Name -> Integer -> Name
uniqName (Name x _) n = Name x (Just n)

----------------------------------------------------------------------

newtype PName = PName String
  deriving (Read, Eq)

instance Show PName where
  show (PName x) = "#" ++ x

pname2name :: PName -> Name
pname2name (PName x) = Name x Nothing

----------------------------------------------------------------------

type Cons = [(PName, Exp)]

data Stmt =
    SDef Name Exp Exp
  | SData PName Exp Cons
  | SDefn PName Exp [Clause]
  deriving (Show, Read, Eq)

data Exp =
    Type | Pi Name Exp Exp | Lam Name Exp Exp
  | Form PName [Exp] | Con PName [Exp]
  | Var Name | Exp :@: Exp | Red PName [Exp]
  deriving (Show, Read, Eq)

type Tel = [(Name, Exp)]
type Sub = [(Name, Exp)]
type PSub = [(Name, Pat)]
type Clause = ([Pat], Exp)

data Sigma =
    Def Name Exp Exp
  | DForm PName Tel
  | DCon PName Tel PName [Exp]
  | DRed PName [Clause] Tel Exp
  deriving (Show, Read, Eq)

data Pat = PVar Name | Inacc (Maybe Exp) | PCon PName [Pat]
  deriving (Show, Read, Eq)

----------------------------------------------------------------------

names :: Tel -> [Name]
names = map fst

varNames :: Tel -> [Exp]
varNames = map (Var . fst)

pvarNames :: Tel -> [Pat]
pvarNames = map (PVar . fst)

pis :: Tel -> Exp -> Exp
pis = flip $ foldr (\ (x , _A) _B -> Pi x _A _B)

lams :: Tel -> Exp -> Exp
lams = flip $ foldr (\ (x , _A) _B -> Lam x _A _B)

apps :: Exp -> [Exp] -> Exp
apps x xs = foldl (:@:) x xs

----------------------------------------------------------------------

formType :: Tel -> Exp
formType _Is = pis _Is Type

conType :: Tel -> PName -> [Exp] -> Exp
conType _As _X _Is = pis _As (Form _X _Is)

----------------------------------------------------------------------
