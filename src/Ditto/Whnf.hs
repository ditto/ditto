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
splitTel _T = do
  _T' <- whnf _T
  case _T' of
    Pi x _A _B -> do
      (rest, end) <- splitTel _B
      return ((x, _A) : rest, end)
    _A -> return ([], _A)

splitApp :: Exp -> TCM (Exp , [Exp])
splitApp b = do
  b' <- whnf b
  case b' of
    f :@: a -> do
      (head, rest) <- splitApp f
      return (head, rest ++ [a])
    otherwise -> return (b' , [])

buildCon :: (Name, Exp) -> TCM Sigma
buildCon (x, _A) = do
  (tel, end) <- splitTel _A
  (head, args) <- splitApp end
  -- TODO check that head is same as datatype name
  case head of
    Var y -> return $ DCon x tel y args
    otherwise -> throwError $ "Head of a constructor is not a type name"
