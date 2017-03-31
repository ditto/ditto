module Ditto.Sub where
import Ditto.Syntax
import Ditto.Monad
import Data.List
import Data.Maybe
import Control.Monad

----------------------------------------------------------------------

fvCtx :: Exp -> TCM [Name]
fvCtx a = flip intersect (fv a) <$> (names <$> getCtx)

----------------------------------------------------------------------

freshen :: Name -> Exp -> TCM (Name, Exp)
freshen x a = do
  x' <- gensymHint x
  a' <- sub1 (x, EVar x') a
  return (x', a')

unbind :: Bind -> TCM (Name, Exp)
unbind (Bind x a) = freshen x a

freshen2 :: Name -> Exp -> Name -> Exp -> TCM (Name, Exp, Exp)
freshen2 x a y b = do
  z <- gensymHint x
  a' <- sub1 (x, EVar z) a
  b' <- sub1 (y, EVar z) b
  return (z, a', b')

unbind2 :: Bind -> Bind -> TCM (Name, Exp, Exp)
unbind2 (Bind x a) (Bind y b) = freshen2 x a y b

----------------------------------------------------------------------

sub1 :: (Name , Exp) -> Exp -> TCM Exp
sub1 xa (EForm y is) = EForm y <$> subs1 xa is
sub1 xa (ECon y as) = ECon y <$> subs1 xa as
sub1 xa (ERed y as) = ERed y <$> subs1 xa as
sub1 xa (EMeta y as) = EMeta y <$> subs1 xa as
sub1 xa (EGuard y) = return $ EGuard y
sub1 (x, a) (EVar y) | x == y = return a
sub1 xa (EVar y) = return $ EVar y
sub1 xa EType = return EType
sub1 xa (EInfer m) = return $ EInfer m
sub1 xa (ELam i _A b) = ELam i <$> sub1 xa _A <*> sub1Bind xa b
sub1 xa (EPi i _A _B) = EPi i <$> sub1 xa _A <*> sub1Bind xa _B
sub1 xa (EApp i f b) = EApp i <$> sub1 xa f <*> sub1 xa b

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

renTel1 :: (Name, Name) -> Tel -> TCM Tel
renTel1 (x, x') [] = return []
renTel1 (x, x') ((i, y, _A):ys) | x == y = do
  ((i, x', _A):) <$> subTel1 (x, EVar x') ys
renTel1 (x, x') ((i, y, _A):ys) = do
  _A <- sub1 (x, EVar x') _A
  ((i, y, _A):) <$> renTel1 (x, x') ys

----------------------------------------------------------------------

freshTel :: Essible -> Tel -> TCM (Tel, Sub)
freshTel e [] = return ([], [])
freshTel e ((i, x, _A):_As) = do
  x' <- gensymEHint e x
  (_As', xs) <- freshTel e =<< subTel1 (x, EVar x') _As
  return ((i, x', _A):_As', (x, EVar x'):xs)

----------------------------------------------------------------------

freshCons :: Con -> TCM Con
freshCons (y, _Bs, is) = do
  (_Bs', xs) <- freshTel Inacc _Bs
  is' <- subs is xs
  return (y, _Bs', is')

lookupConsFresh :: PName -> TCM Cons
lookupConsFresh x = mapM freshCons =<< fromJust <$> lookupCons x

----------------------------------------------------------------------

embedPat :: Pat -> Exp
embedPat (PVar x) = EVar x
embedPat (PCon x as) = apps (EVar (pname2name x)) (embedPats as)
embedPat (PInacc (Just a)) = a
embedPat (PInacc Nothing) = error "Inferred inaccessible cannot be embedded as a term"

embedPats :: Pats -> Args
embedPats = map (\(i, a) -> (i, embedPat a))

embedPSub :: PSub -> Sub
embedPSub = map (\(x, p) -> (x, embedPat p))

injectSub :: Sub -> PSub
injectSub = map (\(x, a) -> (x, injectExp a))

injectExp :: Exp -> Pat
injectExp = PInacc . Just

injectExps :: Args -> Pats
injectExps = map (\(i,a) -> (i, injectExp a))

----------------------------------------------------------------------

ren2sub :: Ren -> Sub
ren2sub = map (\(x, y) -> (x, EVar y))

ren2psub :: Ren -> PSub
ren2psub = map (\(x, y) -> (x, PVar y))

----------------------------------------------------------------------

sub :: Exp -> Sub -> TCM Exp
sub a xs = foldM (flip sub1) a xs

subs :: Args -> Sub -> TCM Args
subs as xs = mapM (\(i, a) -> (i,) <$> sub a xs) as

subTel :: Tel -> Sub -> TCM Tel
subTel _As xs = foldM (flip subTel1) _As xs

renTel :: Tel -> Ren -> TCM Tel
renTel _As xs = foldM (flip renTel1) _As xs

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
