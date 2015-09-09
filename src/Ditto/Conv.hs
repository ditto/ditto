module Ditto.Conv where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Monad
import Ditto.Sub
import Ditto.Pretty
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Applicative
import Text.PrettyPrint.Boxes

----------------------------------------------------------------------

alpha :: Exp -> Exp -> Bool
alpha a b = alpha' [] a b

alpha' :: [(Name, Name)] -> Exp -> Exp -> Bool
alpha' dict Type Type = True
alpha' dict Infer Infer = False
alpha' dict (Form x1 as1) (Form x2 as2) =
  x1 == x2 && all (uncurry (alpha' dict)) (zip as1 as2)
alpha' dict (Con x1 as1) (Con x2 as2) =
  x1 == x2 && all (uncurry (alpha' dict)) (zip as1 as2)
alpha' dict (Red x1 as1) (Red x2 as2) =
  x1 == x2 && all (uncurry (alpha' dict)) (zip as1 as2)
alpha' dict (Meta x1 as1) (Meta x2 as2) =
  x1 == x2 && all (uncurry (alpha' dict)) (zip as1 as2)
alpha' dict (Var x) (Var y) =
  case lookup x dict of
    Nothing -> x == y
    Just x' -> x' == y
alpha' dict (Lam _A1 (Bind x a1)) (Lam _A2 (Bind y a2)) =
  alpha' dict' _A1 _A2 && alpha' dict' a1 a2
    where dict' = (x, y) : dict
alpha' dict (Pi _A1 (Bind x _B1)) (Pi _A2 (Bind y _B2)) =
  alpha' dict' _A1 _A2 && alpha' dict' _B1 _B2
    where dict' = (x, y) : dict
alpha' dict (f1 :@: a1) (f2 :@: a2) =
  alpha' dict f1 f2 && alpha' dict a1 a2
alpha' dict _ _ = False

----------------------------------------------------------------------

conv :: Exp -> Exp -> TCM Exp
conv a b =
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
conv' Infer Infer = throwError "Unelaborated metavariables are unique"
conv' (f1 :@: a1) (f2 :@: a2) =
  (:@:) <$> conv f1 f2 <*> conv a1 a2
conv' (Lam _A1 bnd_b1) (Lam _A2 bnd_b2) = do
  _A' <- conv _A1 _A2
  (x, b1, b2) <- unbind2 bnd_b1 bnd_b2
  b' <- extCtx x _A1 (conv b1 b2)
  return $ Lam _A' (Bind x b')
conv' (Pi _A1 bnd_B1) (Pi _A2 bnd_B2) = do
  _A' <- conv _A1 _A2
  (x, _B1, _B2) <- unbind2 bnd_B1 bnd_B2
  _B' <- extCtx x _A1 (conv _B1 _B2)
  return $ Pi _A' (Bind x _B')
conv' (Form x1 _Is1) (Form x2 _Is2) | x1 == x2 =
  Form x1 <$> mapM (uncurry conv) (zip _Is1 _Is2)
conv' (Form x1 _Is1) (Form x2 _Is2) | x1 /= x2 =
  throwError $ "Type former names not equal"
   ++ show x1 ++ " != "  ++ show x2
conv' (Con x1 as1) (Con x2 as2) | x1 == x2 =
  Con x1 <$> mapM (uncurry conv) (zip as1 as2)
conv' (Con x1 as1) (Con x2 as2) | x1 /= x2 =
  throwError "Constructor names not equal"
conv' (Red x1 as1) (Red x2 as2) | x1 == x2 =
  Red x1 <$> mapM (uncurry conv) (zip as1 as2)
conv' (Red x1 as1) (Red x2 as2) | x1 /= x2 =
  throwError "Reduction names not equal"
conv' (Meta x1 as1) (Meta x2 as2) | x1 == x2 =
  Meta x1 <$> mapM (uncurry conv) (zip as1 as2)
conv' (Meta x1 as1) (Meta x2 as2) | x1 /= x2 =
  throwError "Metavariable names not equal"
conv' a b = throwNotConv a b

----------------------------------------------------------------------
