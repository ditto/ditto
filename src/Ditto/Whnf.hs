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
whnfVirt = local (\ r -> r { rhoExpandable = True }) . whnf'

whnf :: Exp -> TCM Exp
whnf = local (\ r -> r { rhoExpandable = False }) . whnf'

----------------------------------------------------------------------

whnf' :: Exp -> TCM Exp
whnf' Type = return Type
whnf' (f :@: a) = do
  f' <- whnf' f
  a' <- whnf' a
  case f' of
    Lam x _A b -> whnf' $ sub (x , a') b
    otherwise -> return $ f' :@: a'
whnf' (EVar x) = do
  ma <- lookupDef x
  case ma of
    Just a -> whnf' a
    Nothing -> return $ EVar x
whnf' x = return x

----------------------------------------------------------------------