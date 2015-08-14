module Ditto.Conv where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Monad
import Ditto.Sub
import Ditto.Pretty
import Control.Monad.State
import Control.Monad.Except
import Control.Applicative
import Text.PrettyPrint.Boxes

----------------------------------------------------------------------

runConv :: Exp -> Exp -> Either String Exp
runConv a b = runTCM (conv a b)

----------------------------------------------------------------------

alpha :: Exp -> Exp -> Bool
alpha a b = alpha' [] a b

alpha' :: [(Name, Name)] -> Exp -> Exp -> Bool
alpha' dict Type Type = True
alpha' dict (Form x1 as1) (Form x2 as2) =
  x1 == x2 && all (uncurry (alpha' dict)) (zip as1 as2)
alpha' dict (Con x1 as1) (Con x2 as2) =
  x1 == x2 && all (uncurry (alpha' dict)) (zip as1 as2)
alpha' dict (Red x1 as1) (Red x2 as2) =
  x1 == x2 && all (uncurry (alpha' dict)) (zip as1 as2)
alpha' dict (Var x) (Var y) =
  case lookup x dict of
    Nothing -> x == y
    Just x' -> x' == y
alpha' dict (Lam x _A1 a1) (Lam y _A2 a2) =
  alpha' dict' _A1 _A2 && alpha' dict' a1 a2
    where dict' = (x, y) : dict
alpha' dict (Pi x _A1 _B1) (Pi y _A2 _B2) =
  alpha' dict' _A1 _A2 && alpha' dict' _B1 _B2
    where dict' = (x, y) : dict
alpha' dict (f1 :@: a1) (f2 :@: a2) =
  alpha' dict f1 f2 && alpha' dict a1 a2
alpha' dict _ _ = False

----------------------------------------------------------------------

conv :: Exp -> Exp -> TCM Exp
conv a b = do
  if alpha a b
  then return a
  else do
    a' <- whnf a
    b' <- whnf b
    conv' a' b'

conv' :: Exp -> Exp -> TCM Exp
conv' (Var x) (Var y) =
  if x == y
  then return (Var x)
  else throwError $
    "Variables not convertible\n"
    ++ show x ++ " != " ++ show y
conv' Type Type = return Type
conv' (f1 :@: a1) (f2 :@: a2) = do
  f' <- conv f1 f2
  a' <- conv a1 a2
  return $ f' :@: a'
conv' (Lam x1 _A1 b1) (Lam x2 _A2 b2) = do
  _A' <- conv _A1 _A2
  b' <- conv b1 =<< sub (x2, Var x1) b2
  return $ Lam x1 _A' b'
conv' (Pi x1 _A1 _B1) (Pi x2 _A2 _B2) = do
  _A' <- conv _A1 _A2
  _B' <- conv _B1 =<< sub (x2, Var x1) _B2
  return $ Pi x1 _A' _B'
conv' (Form x1 _Is1) (Form x2 _Is2) | x1 == x2 = do
  Form x1 <$> mapM (uncurry conv) (zip _Is1 _Is2)
conv' (Form x1 _Is1) (Form x2 _Is2) | x1 /= x2 =
  throwError "Type former names not equal"
conv' (Con x1 as1) (Con x2 as2) | x1 == x2 = do
  Con x1 <$> mapM (uncurry conv) (zip as1 as2)
conv' (Con x1 as1) (Con x2 as2) | x1 /= x2 =
  throwError "Constructor names not equal"
conv' (Red x1 as1) (Red x2 as2) | x1 == x2 = do
  Red x1 <$> mapM (uncurry conv) (zip as1 as2)
conv' (Red x1 as1) (Red x2 as2) | x1 /= x2 =
  throwError "Reduction names not equal"
conv' a b = do
--  DittoS {sig = sig} <- get
  throwError $
    "Terms not convertible\n"
    ++ show a ++ " != " ++ show b
    -- ++ "\n" ++ unlines (map (render . ppSig) sig)

----------------------------------------------------------------------
