module Ditto.Syntax where
import Data.List
import Data.Maybe

----------------------------------------------------------------------

snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]

reject :: (a -> Bool) -> [a] -> [a]
reject p = filter (not . p)

----------------------------------------------------------------------

data Verbosity = Normal | Verbose
  deriving (Show, Read, Eq)

data Icit = Expl | Impl
  deriving (Show, Read, Eq)

data Essible = Acc | Inacc
  deriving (Show, Read, Eq)

----------------------------------------------------------------------

data Name = Name Essible String (Maybe Integer)
  deriving (Read, Eq)

instance Show Name where
  show (Name e x m) = prefix ++ x ++ suffix
    where
    prefix = case e of Acc -> ""; Inacc -> "."
    suffix = case m of Nothing -> ""; Just n -> "$" ++ show n

s2n :: Essible -> String -> Name
s2n e x = Name e x Nothing

uniqName :: Name -> Integer -> Name
uniqName x@(Name e _ _) n = uniqEName e x n

uniqEName :: Essible -> Name -> Integer -> Name
uniqEName e (Name _ x _) n = Name e x (Just n)

isInacc :: Name -> Bool
isInacc (Name Inacc _ _) = True
isInacc _ = False

----------------------------------------------------------------------

newtype PName = PName String
  deriving (Read, Eq)

instance Show PName where
  show (PName x) = "#" ++ x

pname2name :: PName -> Name
pname2name (PName x) = Name Acc x Nothing

name2pname :: Name -> Maybe PName
name2pname (Name Acc x Nothing) = Just (PName x)
name2pname _ = Nothing

----------------------------------------------------------------------

data MName = MName MKind Integer
  deriving (Read, Eq)

instance Show MName where
  show (MName k n) = "?" ++ prefix k ++ show n
    where
    prefix :: MKind -> String
    prefix MInfer = ""
    prefix (MHole Nothing) = ""
    prefix (MHole (Just nm)) = nm ++ "-"

data MKind = MInfer | MHole (Maybe String)
  deriving (Show, Read, Eq)

----------------------------------------------------------------------

data Stmt =
    SDef Name Exp Exp
  | SData PName Exp Cons
  | SDefn PName Exp [Clause]
  deriving (Show, Read, Eq)

data Sig =
    GDef Name Exp
  | GData PName Exp
  | GDefn PName Exp
  deriving (Show, Read, Eq)

data Bod =
    BDef Name Exp
  | BData PName Cons
  | BDefn PName [Clause]
  deriving (Show, Read, Eq)

data Exp =
    Type | Pi Icit Exp Bind | Lam Icit Exp Bind
  | Form PName Args | Con PName Args
  | Red PName Args | Meta MName Args
  | Var Name | App Icit Exp Exp | Infer MKind
  deriving (Show, Read, Eq)

data Bind = Bind Name Exp
  deriving (Show, Read, Eq)

type Prog = [MStmt]
type MStmt = Either Stmt [Stmt]
type Cons = [(PName, Exp)]
type Arg = (Icit, Exp)
type Args = [Arg]
type Env = [Sigma]
type Tel = [(Icit, Name, Exp)]
type Ren = [(Name, Name)]
type Sub = [(Name, Exp)]
type PSub = [(Name, Pat)]
type Clause = (Pats, RHS)
type CheckedClause = (Tel, Pats, RHS)
type ConSig = (PName, Tel, Args)
type Pats = [(Icit, Pat)]
type Hole = (MName, Tel, Exp)
type Holes = [Hole]
type Acts = [(Tel, Act)]
type CtxErr = ([Name], Prog, Acts, Tel, Err)

data RHS = MapsTo Exp | Caseless Name | Split Name
  deriving (Show, Read, Eq)

data Sigma =
    Def Name (Maybe Exp) Exp
  | DForm PName [ConSig] Tel
  | DRed PName [CheckedClause] Tel Exp
  | DMeta MName (Maybe Exp) Tel Exp
  deriving (Show, Read, Eq)

data Pat = PVar Name | PInacc (Maybe Exp) | PCon PName Pats
  deriving (Show, Read, Eq)

data Act =
    AInfer Exp
  | ACheck Exp Exp
  | AConv Exp Exp
  | ACover PName Pats
  | ADef Name
  | AData PName
  | ACon PName
  | ADefn PName
  deriving (Show, Read, Eq)

data Err =
    EGen String
  | EConv Exp Exp
  | EScope Name
  | ECaseless Name
  | EMetas Holes
  | ECover Tel PName Pats
  | EReach PName [Clause]
  | ESplit [CheckedClause]
  | EAtom Exp
  deriving (Show, Read, Eq)

----------------------------------------------------------------------

toSig :: Stmt -> Sig
toSig (SDef x _ _A) = GDef x _A
toSig (SData x _A _) = GData x _A
toSig (SDefn x _A _) = GDefn x _A

toBod :: Stmt -> Bod
toBod (SDef x a _) = BDef x a
toBod (SData x _ cs) = BData x cs
toBod (SDefn x _ cs) = BDefn x cs

----------------------------------------------------------------------

names :: Tel -> [Name]
names = map $ \(_,x,_) -> x

lookupTel :: Name -> Tel -> Maybe Exp
lookupTel x = lookup x . map (\(_,x,a) -> (x, a))

varArgs :: Tel -> Args
varArgs = map $ \(i,x,_) -> (i, Var x)

pvarPats :: Tel -> Pats
pvarPats = map (\(i, x, _) -> (i, PVar x))

pis :: Tel -> Exp -> Exp
pis = flip $ foldr $ \ (i, x, _A) _B -> Pi i _A (Bind x _B)

ipis :: Tel -> Exp -> Exp
ipis as = pis (map (\(_,x,a) -> (Impl,x,a)) as)

paramCons :: Tel -> Cons -> Cons
paramCons _As = map (\(x, _A) -> (x, ipis _As _A))

lams :: Tel -> Exp -> Exp
lams = flip $ foldr $ \ (i, x , _A) _B -> Lam i _A (Bind x _B)

apps :: Exp -> Args -> Exp
apps = foldl $ \ f (i, a) -> App i f a

hole :: Exp
hole = Infer (MHole Nothing)

----------------------------------------------------------------------

formType :: Tel -> Exp
formType _Is = pis _Is Type

conType :: Tel -> PName -> Args -> Exp
conType _As _X _Is = pis _As (Form _X _Is)

----------------------------------------------------------------------

viewSpine :: Exp -> (Exp, Args)
viewSpine (App i f a) = (g, snoc as (i, a))
  where (g, as) = viewSpine f
viewSpine x = (x, [])

----------------------------------------------------------------------

fv :: Exp -> [Name]
fv (Var x) = [x]
fv Type = []
fv (Infer _) = []
fv (Form _ is) = fvs is
fv (Con _ as) = fvs as
fv (Red _ as) = fvs as
fv (Meta _ as) = fvs as
fv (Pi _ _A _B) = fv _A ++ fvBind _B
fv (Lam _ _A b) = fv _A ++ fvBind b
fv (App _ a b) = fv a ++ fv b

fvs :: Args -> [Name]
fvs as = concatMap fv (map snd as)

fvBind :: Bind -> [Name]
fvBind (Bind n b) = n `delete` nub (fv b)

fvTel :: Tel -> [Name]
fvTel [] = []
fvTel ((_, _X, _A):_As) = fv _A ++ (_X `delete` nub (fvTel _As))

fvRHS :: RHS -> [Name]
fvRHS (MapsTo a) = fv a
fvRHS (Caseless x) = [x]
fvRHS (Split x) = [x]

fvPats :: Pats -> [Name]
fvPats = concatMap (\(i,p) -> fvPat p)

fvPat :: Pat -> [Name]
fvPat (PVar x) = [x]
fvPat (PInacc _) = []
fvPat (PCon _ ps) = fvPats ps

----------------------------------------------------------------------

isNamed :: Name -> Sigma -> Bool
isNamed x (Def y _ _) = x == y
isNamed x _ = False

isPNamed :: PName -> Sigma -> Bool
isPNamed x (DForm y (conNames -> ys) _) = x == y || any (x==) ys
isPNamed x (DRed y _ _ _) = x == y
isPNamed x _ = False

conNames :: [ConSig] -> [PName]
conNames = map conName

conName :: ConSig -> PName
conName (x, _, _) = x

isMNamed :: MName -> Sigma -> Bool
isMNamed x (DMeta y _ _ _) = x == y
isMNamed x _ = False

isDef :: Sigma -> Bool
isDef (Def _ _ _) = True
isDef _ = False

isMeta :: Sigma -> Bool
isMeta (DMeta _ _ _ _) = True
isMeta _ = False

filterDefs :: Env -> [(Name, Maybe Exp, Exp)]
filterDefs = catMaybes . map envDef . filter isDef

defNames :: Env -> [Name]
defNames = map (\(x,_,_) -> x) . filterDefs

envDef :: Sigma -> Maybe (Name, Maybe Exp, Exp)
envDef (Def x a _A) = Just (x, a, _A)
envDef _ = Nothing

envDefType :: Sigma -> Maybe Exp
envDefType (Def _ _ _A) = Just _A
envDefType _ = Nothing

envDefBody :: Sigma -> Maybe Exp
envDefBody (Def _ a _) = a
envDefBody _ = Nothing

isHole :: MName -> Bool
isHole (MName (MHole _) _) = True
isHole (MName _ _) = False

envUndefMeta :: Sigma -> Maybe Hole
envUndefMeta (DMeta x Nothing _As _B) | not (isHole x) = Just (x, _As, _B)
envUndefMeta _ = Nothing

envHole :: Sigma -> Maybe Hole
envHole (DMeta x ma _As _B) | isHole x = Just (x, _As, _B)
envHole _ = Nothing

envMetaBody :: Sigma -> Maybe Exp
envMetaBody (DMeta _ (Just a) _ _) = Just a
envMetaBody _ = Nothing

envMetaType :: Sigma -> Maybe (Tel, Exp)
envMetaType (DMeta _ _ _As _B) = Just (_As, _B)
envMetaType _ = Nothing

conSig :: PName -> Sigma -> Maybe ConSig
conSig x (DForm _X cs _) = case find (\c -> x == conName c) cs of
  Just (x, _As, is) -> Just (_X, _As, is)
  Nothing -> Nothing
conSig x _ = Nothing

conSigs :: Sigma -> Maybe [ConSig]
conSigs (DForm _ cs _) = Just cs
conSigs _ = Nothing

redType :: Sigma -> Maybe (Tel, Exp)
redType (DRed _ _ _As _B) = Just (_As, _B)
redType _ = Nothing

redClauses :: Sigma -> Maybe [CheckedClause]
redClauses (DRed _ cs _ _) = Just cs
redClauses _ = Nothing

----------------------------------------------------------------------
