module Ditto.Whnf where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Data.Maybe
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except

----------------------------------------------------------------------

runWhnf :: Exp -> Either String Exp
runWhnf a = runTCM (whnf a)

----------------------------------------------------------------------

whnf :: Exp -> TCM Exp
whnf (f :@: a) = do
  a' <- whnf a
  whnf f >>= \case
    Lam _A xb -> do
      (x, b) <- unbind xb
      whnf =<< sub1 (x , a') b
    f' -> return $ f' :@: a'
whnf (Red x as) = do
  cs <- fromJust <$> lookupRedClauses x
  betaRed x (map (\(_, ps, rhs) -> (ps, rhs)) cs) as
whnf (Var x) = lookupDef x >>= \case
  Just a -> whnf a
  Nothing -> return $ Var x
whnf x = return x

----------------------------------------------------------------------

betaRed :: PName -> [Clause] -> [Exp] -> TCM Exp
betaRed x [] as = return $ Red x as
betaRed x ((ps, rhs):cs) as = matchExps ps as >>= \case
  Just xs -> case rhs of
    Prog a -> whnf =<< sub a xs
    Caseless y -> throwError "Reducing a caseless RHS"
  Nothing -> betaRed x cs as

matchExps :: [Pat] -> [Exp] -> TCM (Maybe Sub)
matchExps ps as = do
  ms <- mapM (uncurry matchExp) (zip ps as)
  return (Just . concat =<< sequence ms)

matchExp :: Pat -> Exp -> TCM (Maybe Sub)
matchExp p a = matchExp' p =<< whnf a

matchExp' :: Pat -> Exp -> TCM (Maybe Sub)
matchExp' (PVar x) a = return $ Just [(x, a)]
matchExp' (Inacc _) a = return $ Just []
matchExp' (PCon x ps) (Con y as) | x == y = matchExps ps as
matchExp' _ _ = return Nothing

----------------------------------------------------------------------

splitTel :: Exp -> TCM (Tel , Exp)
splitTel _T = whnf _T >>= \case
  Pi _A bnd_B -> do
    (x, _B) <- unbind bnd_B
    (rest, end) <- extCtx x _A (splitTel _B)
    return ((x, _A) : rest, end)
  _A -> return ([], _A)

buildCon :: PName -> (PName, Exp) -> TCM (PName, Tel, PName, [Exp])
buildCon _X (x, _A) = do
  (tel, end) <- splitTel _A
  extCtxs tel (whnf end) >>= \case
    Form _Y _Is | _X == _Y -> return (x , tel, _Y, _Is)
    Form _Y _Is -> throwError $ "Constructor type does not match datatype\n"
      ++ show _X ++ " != " ++ show _Y
    otherwise -> throwError "Constructor return type is not a type former"

----------------------------------------------------------------------