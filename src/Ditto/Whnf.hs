module Ditto.Whnf where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Control.Monad.Reader
import Control.Monad.Except

----------------------------------------------------------------------

runWhnf :: Exp -> Either String Exp
runWhnf a = runTCM (whnf a)

----------------------------------------------------------------------

whnfVirt :: Exp -> TCM Exp
whnfVirt = whnf' Rho

whnf :: Exp -> TCM Exp
whnf = whnf' BetaDelta

----------------------------------------------------------------------

whnf' :: Normality -> Exp -> TCM Exp
whnf' n (f :@: a) = do
  f' <- whnf' n f
  a' <- whnf' n a
  case f' of
    Lam x _A b -> whnf' n =<< sub (x , a') b
    otherwise -> return $ f' :@: a'
whnf' n (Var x) = do
  ma <- lookupDef n x
  case ma of
    Just a -> whnf' n a
    Nothing -> return $ Var x
whnf' n x = return x

----------------------------------------------------------------------

splitTel :: Exp -> TCM (Tel , Exp)
splitTel _A = do
  _A' <- whnf _A
  case _A' of
   (Pi x _A a) -> do
     (rest, end) <- splitTel a
     return ((x, _A) : rest, end)
   a -> return ([], a)

splitApp :: Exp -> TCM (Exp , [Exp])
splitApp a = do
  a' <- whnf a
  case a of
   f :@: b -> do
     (head, rest) <- splitApp b
     return (head, rest ++ [b])
   a -> return (a , [])

buildCon :: (Name, Exp) -> TCM Sigma
buildCon (x, _A) = do
  (tel, _A') <- splitTel _A
  (head, pars) <- splitApp _A'
  case head of
   Var y -> return $ DCon x tel y pars
   otherwise -> throwError $ "Head of a constructor is not a type name"
