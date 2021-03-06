module Ditto.Whnf where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Data.Maybe

----------------------------------------------------------------------

whnf :: Exp -> TCM Exp
whnf (EApp i1 f a) = whnf f >>= \case
  ELam i2 _A xb | i1 == i2 -> do
    (x, b) <- unbind xb
    whnf =<< sub1 (x , a) b
  f' -> return $ EApp i1 f' a
whnf (ERed x as) = do
  cs <- lookupClauses x
  betaRed x (map (\(Clause _ ps rhs) -> (ps, rhs)) cs) as
whnf (EVar x) = lookupDef x >>= \case
  Just a -> whnf a
  Nothing -> return $ EVar x
whnf (EMeta x as) = lookupSol x >>= \case
  Just a -> whnf (apps a as)
  Nothing -> return $ EMeta x as
whnf (EGuard x) = lookupGuard x >>= \case
  Just a -> whnf a
  Nothing -> return $ EGuard x
whnf x = return x

----------------------------------------------------------------------

betaRed :: PName -> SClauses -> Args -> TCM Exp
betaRed x [] as = return $ ERed x as
betaRed x ((ps, rhs):cs) as = matchExps ps as >>= \case
  Just xs -> case rhs of
    MapsTo a -> whnf =<< sub a xs
    Caseless y -> error "Reducing a caseless RHS"
    Split y -> error "Reducing a splitting RHS"
  Nothing -> betaRed x cs as

matchExps :: Pats -> Args -> TCM (Maybe Sub)
matchExps ps as = do
  ms <- mapM (uncurry matchExp) (zip ps as)
  return (Just . concat =<< sequence ms)

matchExp :: (Icit, Pat) -> (Icit, Exp) -> TCM (Maybe Sub)
matchExp (i1, p) (i2, a) | i1 == i2 = matchExp' p =<< whnf a
matchExp (i1, p) (i2, a) = return Nothing

matchExp' :: Pat -> Exp -> TCM (Maybe Sub)
matchExp' (PVar x) a = return $ Just [(x, a)]
matchExp' (PInacc _) a = return $ Just []
matchExp' (PCon x ps) (ECon _ y as) | x == y = matchExps ps as
matchExp' _ _ = return Nothing

----------------------------------------------------------------------

prefixTel :: Exp -> Icits -> TCM (Tel , Exp)
prefixTel _A [] = return ([] , _A)
prefixTel _AB (i:is) = whnf _AB >>= \case
  EPi j _A bnd_B | i == j -> do
    (x, _B) <- unbind bnd_B
    (tel, end) <- prefixTel _B is
    return ((j, x, _A):tel, end)
  EPi Impl _A bnd_B -> do
    (x, _B) <- unbind bnd_B
    (tel, end) <- prefixTel _B (i:is)
    return ((Impl, x, _A):tel, end)
  otherwise -> error "Patterns expect a function type"

splitTel :: Exp -> TCM (Tel , Exp)
splitTel _AB = whnf _AB >>= \case
  EPi i _A bnd_B -> do
    (x, _B) <- unbind bnd_B
    (rest, end) <- splitTel _B
    return ((i, x, _A) : rest, end)
  _A -> return ([], _A)

buildCon :: PName -> (PName, Exp) -> TCM (PName, Tel, PName, Args)
buildCon _X (x, _A) = do
  (tel, end) <- splitTel _A
  extCtxs tel $ whnf end >>= \case
    EForm _Y _Is | _X == _Y -> return (x , tel, _Y, _Is)
    EForm _Y _Is -> error "Constructor type does not match datatype"
    otherwise -> error "Constructor return type is not a type former"

----------------------------------------------------------------------
