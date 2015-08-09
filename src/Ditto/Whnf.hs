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

-- TODO rho expand Form with virtual definition, not variables
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

buildCon :: PName -> (PName, Exp) -> TCM (PName, Tel, PName, [Exp])
buildCon _X (x, _A) = do
  (tel, end) <- splitTel _A
  end' <- whnf end
  case end' of
    Form _Y _Is | _X == _Y -> return $ (x , tel, _Y, _Is)
    Form _Y _Is -> throwError $ "Constructor type does not match datatype\n"
      ++ show _X ++ " != " ++ show _Y
    otherwise -> throwError "Constructor return type is not a type former"

----------------------------------------------------------------------

-- buildElimType :: PName -> TCM Exp
-- buildElimType x = do

----------------------------------------------------------------------