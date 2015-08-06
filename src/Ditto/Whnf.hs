module Ditto.Whnf where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Control.Monad.Except

whnf :: Exp -> TCM Exp
whnf (f :@: a) = do
  f' <- whnf f
  a' <- whnf a
  case f' of
    Lam x _A b -> whnf $ sub (x , a') b
    otherwise -> return $ f' :@: a'
whnf (EVar x) = do
  ma <- lookupDef x
  case ma of
    Just a -> whnf a
    Nothing -> return $ EVar x
whnf x = return x
