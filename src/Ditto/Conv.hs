module Ditto.Conv where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Monad
import Ditto.Sub
import Control.Monad.Except

alpha :: Exp -> Exp -> TCM Bool
alpha a b = error "alpha equality not defined"

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
