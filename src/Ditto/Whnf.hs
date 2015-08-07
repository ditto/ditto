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
    Lam x _A b -> whnf' n $ sub (x , a') b
    otherwise -> return $ f' :@: a'
whnf' n (EVar x) = do
  ma <- lookupDef n x
  case ma of
    Just a -> whnf' n a
    Nothing -> return $ EVar x
whnf' n x = return x

----------------------------------------------------------------------