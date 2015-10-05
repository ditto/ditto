module Ditto.Sub where
import Ditto.Syntax
import Ditto.Monad
import Data.List
import Control.Applicative
import Control.Monad

----------------------------------------------------------------------

fvCtx :: Exp -> TCM [Name]
fvCtx a = flip intersect (fv a) <$> (names <$> getCtx)

----------------------------------------------------------------------

freshen :: Name -> Exp -> TCM (Name, Exp)
freshen x a = do
  x' <- gensymHint x
  a' <- sub1 (x, Var x') a
  return (x', a')

unbind :: Bind -> TCM (Name, Exp)
unbind (Bind x a) = freshen x a

freshen2 :: Name -> Exp -> Name -> Exp -> TCM (Name, Exp, Exp)
freshen2 x a y b = do
  z <- gensymHint x
  a' <- sub1 (x, Var z) a
  b' <- sub1 (y, Var z) b
  return (z, a', b')

unbind2 :: Bind -> Bind -> TCM (Name, Exp, Exp)
unbind2 (Bind x a) (Bind y b) = freshen2 x a y b

----------------------------------------------------------------------

sub1 :: (Name , Exp) -> Exp -> TCM Exp
sub1 xa (Form y is) = Form y <$> subs1 xa is
sub1 xa (Con y as) = Con y <$> subs1 xa as
sub1 xa (Red y as) = Red y <$> subs1 xa as
sub1 xa (Meta y as) = Meta y <$> subs1 xa as
sub1 (x, a) (Var y) | x == y = return a
sub1 xa (Var y) = return $ Var y
sub1 xa Type = return Type
sub1 xa (Infer m) = return $ Infer m
sub1 xa (Lam i _A b) = Lam i <$> sub1 xa _A <*> sub1Bind xa b
sub1 xa (Pi i _A _B) = Pi i <$> sub1 xa _A <*> sub1Bind xa _B
sub1 xa (App i f b) = App i <$> sub1 xa f <*> sub1 xa b

subs1 :: (Name , Exp) -> Args -> TCM Args
subs1 xa = mapM (\(i, a) -> (i,) <$> sub1 xa a)

sub1Bind :: (Name , Exp) -> Bind -> TCM Bind
sub1Bind (x, a) (Bind y b) | x == y = pure $ Bind y b
sub1Bind (x, a) (Bind y b) | y `notElem` fv a = Bind y <$> sub1 (x, a) b
sub1Bind (x, a) (Bind y b) = do
  (y', b') <- freshen y b
  Bind y' <$> sub1 (x, a) b'

subTel1 :: (Name, Exp) -> Tel -> TCM Tel
subTel1 xa = mapM (\(i, y, _A) -> (i,y,) <$> sub1 xa _A)

----------------------------------------------------------------------

freshTel :: Essible -> Tel -> TCM (Tel, Sub)
freshTel e [] = return ([], [])
freshTel e ((i, x, _A):_As) = do
  x' <- gensymEHint e x
  (_As', xs) <- freshTel e =<< subTel1 (x, Var x') _As
  return ((i, x', _A):_As', (x, Var x'):xs)

----------------------------------------------------------------------

freshCons :: Essible -> (PName, Tel, Args) -> TCM (PName, Tel, Args)
freshCons e (y, _Bs, is) = do
  (_Bs', xs) <- freshTel e _Bs
  is' <- subs is xs
  return (y, _Bs', is')

lookupConsFresh :: Essible -> PName -> TCM [(PName, Tel, Args)]
lookupConsFresh e x = mapM (freshCons e) =<< lookupCons x

----------------------------------------------------------------------

embedPat :: Pat -> Exp
embedPat (PVar x) = Var x
embedPat (PCon x as) = apps (Var (pname2name x)) (embedPats as)
embedPat (PInacc (Just a)) = a
embedPat (PInacc Nothing) = error "Inferred inaccessible cannot be embedded as a term"

embedPats :: Pats -> Args
embedPats = map $ \(i, a) -> (i, embedPat a)

embedPSub :: PSub -> Sub
embedPSub = map (\ (x, p) -> (x, embedPat p))

injectSub :: Sub -> PSub
injectSub = map (\(x, a) -> (x, PInacc (Just a)))

----------------------------------------------------------------------

sub :: Exp -> Sub -> TCM Exp
sub a xs = foldM (flip sub1) a xs

subs :: Args -> Sub -> TCM Args
subs as xs = mapM (\(i, a) -> (i,) <$> sub a xs) as

subTel :: Tel -> Sub -> TCM Tel
subTel _As xs = foldM (flip subTel1) _As xs

psub :: Exp -> PSub -> TCM Exp
psub a xs = sub a (embedPSub xs)

psubTel1 :: (Name, Pat) -> Tel -> TCM Tel
psubTel1 (x, p) _As = subTel1 (x, embedPat p) _As

psubTel :: Tel -> PSub -> TCM Tel
psubTel _As qs = subTel _As (embedPSub qs)

mkSub :: Tel -> Args -> Sub
mkSub _As as = zip (names _As) (map snd as)

----------------------------------------------------------------------

psubPat :: Pat -> PSub -> TCM Pat
psubPat (PVar x) xs = return $ maybe (PVar x) id (lookup x xs)
psubPat (PCon x ps) xs = PCon x <$> psubPats ps xs
psubPat (PInacc Nothing) xs = return $ PInacc Nothing
psubPat (PInacc (Just a)) xs = PInacc . Just <$> psub a xs

psubPats :: Pats -> PSub -> TCM Pats
psubPats ps xs = mapM (\(i, p) -> (i,) <$> psubPat p xs) ps

subClauseType :: Exp -> Tel -> Pats -> TCM Exp
subClauseType _B _As ps = psub _B (zip (names _As) (map snd ps))

----------------------------------------------------------------------
