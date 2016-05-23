module Ditto.Whnf where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Data.Maybe

----------------------------------------------------------------------

whnf :: Exp -> TCM Exp
whnf (App i1 f a) = whnf f >>= \case
  Lam i2 _A xb | i1 == i2 -> do
    (x, b) <- unbind xb
    whnf =<< sub1 (x , a) b
  _ -> return $ App i1 f a
whnf (Red x as) = do
  cs <- fromJust <$> lookupRedClauses x
  betaRed x (map (\(_, ps, rhs) -> (ps, rhs)) cs) as
whnf (Var x) = lookupDef x >>= \case
  Just a -> whnf a
  Nothing -> return $ Var x
whnf (Meta x as) = lookupMeta x >>= \case
  Just a -> whnf (apps a as)
  Nothing -> return $ Meta x as
whnf (Guard x) = lookupGuard x >>= \case
  Just a -> whnf a
  Nothing -> return $ Guard x
whnf x = return x

----------------------------------------------------------------------

betaRed :: PName -> [Clause] -> Args -> TCM Exp
betaRed x [] as = return $ Red x as
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
matchExp' (PCon x ps) (Con y as) | x == y = matchExps ps as
matchExp' _ _ = return Nothing

----------------------------------------------------------------------

splitTel :: Exp -> TCM (Tel , Exp)
splitTel _T = whnf _T >>= \case
  Pi i _A bnd_B -> do
    (x, _B) <- unbind bnd_B
    (rest, end) <- splitTel _B
    return ((i, x, _A) : rest, end)
  _A -> return ([], _A)

buildCon :: PName -> (PName, Exp) -> TCM (PName, Tel, PName, Args)
buildCon _X (x, _A) = do
  (tel, end) <- splitTel _A
  extCtxs tel $ whnf end >>= \case
    Form _Y _Is | _X == _Y -> return (x , tel, _Y, _Is)
    Form _Y _Is -> error "Constructor type does not match datatype"
    otherwise -> error "Constructor return type is not a type former"

whnfHole :: Hole -> TCM Hole
whnfHole (x, _As, _B) = do
  _As <- mapM (\(i, x, _A) -> (i,x,) <$> whnf _A) _As
  _B <- whnf _B
  return (x, _As, _B)

whnfHoles :: Holes -> TCM Holes
whnfHoles = mapM whnfHole

----------------------------------------------------------------------
