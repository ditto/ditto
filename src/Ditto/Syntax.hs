module Ditto.Syntax where

----------------------------------------------------------------------

type Name = String
type Cons = [(PName, Exp)]

data Stmt = SDef Name Exp Exp
          | SData PName Exp Cons
  deriving (Show, Read, Eq)

newtype PName = PName { fromPName :: Name }
  deriving (Read, Eq)

instance Show PName where
  show (PName x) = "#" ++ x

data Exp =
    Type | Pi Name Exp Exp | Lam Name Exp Exp
  | Form PName [Exp] | Con PName [Exp] | Elim PName [Exp]
  | Var Name | Exp :@: Exp
  deriving (Show, Read, Eq)

type Tel = [(Name, Exp)]

data Sigma =
    Def Name Exp Exp
  | Virt Name Exp Exp
  | DForm PName Tel
  | DCon PName Tel PName [Exp]
  deriving (Show, Read, Eq)

data Pat = PVar Name | Inacc Exp | PCon Name [Pat]
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

-- TODO add inductive hypotheses
elimMethod :: PName -> Name -> (Name, PName, Tel, [Exp]) -> (Name, Exp)
elimMethod _X _P (m, c, _As, is) = (m, pis _As (apps (Var _P : [(Con c is)])))

elimTarget :: PName -> Name -> Tel -> (Name, Exp)
elimTarget _X t _Is = (t, Form _X (varNames _Is))

elimMotive :: PName -> Name -> Name -> Tel -> (Name, Exp)
elimMotive _X _P t _Is = (_P, pis (_Is ++ [elimTarget _X t _Is]) Type)

elimType :: PName -> (Name, Name, Tel, [(Name, PName, Tel, [Exp])]) -> (Tel, Exp)
elimType _X (t, _P, _Is, _Cs) =
    ( (_Is ++ [elimMotive _X _P t _Is] ++ [elimTarget _X t _Is] ++ map (elimMethod _X _P) _Cs)
    , (apps ((Var _P) : (varNames _Is) ++ [Var t])))

----------------------------------------------------------------------
