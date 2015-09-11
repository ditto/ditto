module Ditto.Syntax where

----------------------------------------------------------------------

data Verbosity = Normal | Verbose
  deriving (Show, Read, Eq)

data Icit = Expl | Impl
  deriving (Show, Read, Eq)

----------------------------------------------------------------------

data Name = Name String (Maybe Integer)
  deriving (Read, Eq)

instance Show Name where
  show (Name x Nothing) = x
  show (Name x (Just n)) = x ++ "$" ++ show n

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

name2pname :: Name -> Maybe PName
name2pname (Name x Nothing) = Just (PName x)
name2pname _ = Nothing

----------------------------------------------------------------------

newtype MName = MName Integer
  deriving (Read, Eq)

instance Show MName where
  show (MName n) = "?" ++ show n

----------------------------------------------------------------------

type Cons = [(PName, Exp)]

data Stmt =
    SDef Name Exp Exp
  | SData PName Exp Cons
  | SDefn PName Exp [Clause]
  deriving (Show, Read, Eq)

data Exp =
    Type | Pi Icit Exp Bind | Lam Icit Exp Bind
  | Form PName Args | Con PName Args
  | Red PName Args | Meta MName Args
  | Var Name | App Icit Exp Exp | Infer
  deriving (Show, Read, Eq)

data Bind = Bind Name Exp
  deriving (Show, Read, Eq)

type Arg = (Icit, Exp)
type Args = [Arg]
type Env = [Sigma]
type Ctx = [(Name, Exp)]
type Tel = [(Icit, Name, Exp)]
type Sub = [(Name, Exp)]
type PSub = [(Name, Pat)]
type Clause = (Pats, RHS)
type CheckedClause = (Ctx, Pats, RHS)
type Pats = [(Icit, Pat)]

data RHS = Prog Exp | Caseless Name
  deriving (Show, Read, Eq)

data Sigma =
    Def Name Exp Exp
  | DForm PName Tel
  | DCon PName Tel PName Args
  | DRed PName [CheckedClause] Tel Exp
  | DMeta MName (Maybe Exp) Tel Exp
  deriving (Show, Read, Eq)

data Pat = PVar Name | Inacc (Maybe Exp) | PCon PName Pats
  deriving (Show, Read, Eq)

----------------------------------------------------------------------

-- contexts are in semantic order, so reverse them
toTel :: Ctx -> Tel
toTel = reverse . map (\(x, _A) -> (Expl, x, _A))

-- telescopes are in legible order, so reverse them
fromTel :: Tel -> Ctx
fromTel = reverse. map (\(_, x, _A) -> (x, _A))

names :: Tel -> [Name]
names = map $ \(_,x,_) -> x

varArgs :: Tel -> Args
varArgs = map $ \(i,x,_) -> (i, Var x)

pvarPats :: Tel -> Pats
pvarPats = map (\(i, x, _) -> (i, PVar x))

pis :: Tel -> Exp -> Exp
pis = flip $ foldr $ \ (i, x, _A) _B -> Pi i _A (Bind x _B)

lams :: Tel -> Exp -> Exp
lams = flip $ foldr $ \ (i, x , _A) _B -> Lam i _A (Bind x _B)

apps :: Exp -> Args -> Exp
apps = foldl $ \ f (i, a) -> App i f a

----------------------------------------------------------------------

formType :: Tel -> Exp
formType _Is = pis _Is Type

conType :: Tel -> PName -> Args -> Exp
conType _As _X _Is = pis _As (Form _X _Is)

metaType :: Tel -> Exp -> Exp
metaType _As _B = pis _As _B

----------------------------------------------------------------------
