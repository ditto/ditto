module Ditto.Conv where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Monad
import Ditto.Sub
import Control.Monad.Except
import Control.Applicative

alpha :: Exp -> Exp -> TCM Bool
alpha a b = alpha' [] a b

alpha' :: [(Name, Name)] -> Exp -> Exp -> TCM Bool
alpha' dict (EVar x) (EVar y) =
  return $ case lookup x dict of
    Nothing -> x == y
    Just x' -> x' == y
alpha' dict (Lam x _A1 a1) (Lam y _A2 a2) =
  (&&) <$> alpha' dict' _A1 _A2 <*> alpha' dict' a1 a2
    where dict' = (x, y) : dict
alpha' dict (Pi x _A1 _B1) (Pi y _A2 _B2) =
  (&&) <$> alpha' dict' _A1 _A2 <*> alpha' dict' _B1 _B2
    where dict' = (x, y) : dict
alpha' dict (f1 :@: a1) (f2 :@: a2) =
  (&&) <$> alpha' dict f1 f2 <*> alpha' dict a1 a2
alpha' dict Type Type = return True
alpha' dict _ _ = return False

-- TODO we rho expand eagerly, which may be wrong
conv :: Exp -> Exp -> TCM Exp
conv a b = do
  q <- alpha a b
  if q
  then return a
  else do
    a' <- whnfVirt a
    b' <- whnfVirt b
    conv' a' b'

conv' :: Exp -> Exp -> TCM Exp
conv' (EVar x) (EVar y) =
  if x == y
  then return (EVar x)
  else throwError "Variables not convertible"
conv' Type Type = return Type
conv' (f1 :@: a1) (f2 :@: a2) = do
  f' <- conv f1 f2
  a' <- conv a1 a2
  return $ f' :@: a'
conv' (Lam x1 _A1 b1) (Lam x2 _A2 b2) = do
  _A' <- conv _A1 _A2
  b' <- conv b1 (sub (x2, EVar x1) b2)
  return $ Lam x1 _A' b'
conv' (Pi x1 _A1 _B1) (Pi x2 _A2 _B2) = do
  _A' <- conv _A1 _A2
  _B' <- conv _B1 (sub (x2, EVar x1) _B2)
  return $ Pi x1 _A' _B'
conv' a b = throwError "Terms not convertible"
