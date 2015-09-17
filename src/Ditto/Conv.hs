module Ditto.Conv where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Monad
import Ditto.Sub
import Ditto.Env
import Ditto.Pretty
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Applicative
import Data.List
import Text.PrettyPrint.Boxes

----------------------------------------------------------------------

alpha :: Exp -> Exp -> Bool
alpha a b = alpha' [] a b

alpha' :: [(Name, Name)] -> Exp -> Exp -> Bool
alpha' dict Type Type = True
alpha' dict (Infer _) (Infer _) = False
alpha' dict (Form x1 as1) (Form x2 as2) =
  x1 == x2 && alphas' dict as1 as2
alpha' dict (Con x1 as1) (Con x2 as2) =
  x1 == x2 && alphas' dict as1 as2
alpha' dict (Red x1 as1) (Red x2 as2) =
  x1 == x2 && alphas' dict as1 as2
alpha' dict (Meta x1 as1) (Meta x2 as2) =
  x1 == x2 && alphas' dict as1 as2
alpha' dict (Var x) (Var y) =
  case lookup x dict of
    Nothing -> x == y
    Just x' -> x' == y
alpha' dict (Lam i1 _A1 (Bind x a1)) (Lam i2 _A2 (Bind y a2)) =
  i1 == i2 && alpha' dict' _A1 _A2 && alpha' dict' a1 a2
    where dict' = (x, y) : dict
alpha' dict (Pi i1 _A1 (Bind x _B1)) (Pi i2 _A2 (Bind y _B2)) =
  i1 == i2 && alpha' dict' _A1 _A2 && alpha' dict' _B1 _B2
    where dict' = (x, y) : dict
alpha' dict (App i1 f1 a1) (App i2 f2 a2) =
  i1 == i2 && alpha' dict f1 f2 && alpha' dict a1 a2
alpha' dict _ _ = False

alphas' :: [(Name, Name)] -> Args -> Args -> Bool
alphas' dict as1 as2 = all
  (\((i1, a1) , (i2, a2)) -> i1 == i2 && alpha' dict a1 a2)
  (zip as1 as2)

----------------------------------------------------------------------

conv :: Exp -> Exp -> TCM Exp
conv a b = during (AConv a b) $
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
  else throwErr (EConv (Var x) (Var y))
conv' Type Type = return Type
conv' (Infer _) (Infer _) = throwGenErr "Unelaborated metavariables are unique"
conv' (App i1 f1 a1) (App i2 f2 a2) | i1 == i2 =
  App i1 <$> conv f1 f2 <*> conv a1 a2
conv' (Lam i1 _A1 bnd_b1) (Lam i2 _A2 bnd_b2) | i1 == i2 = do
  (x, b1, b2) <- unbind2 bnd_b1 bnd_b2
  b' <- extCtx x _A1 (conv b1 b2)
  return $ Lam i1 _A1 (Bind x b')
conv' (Pi i1 _A1 bnd_B1) (Pi i2 _A2 bnd_B2) | i1 == i2 = do
  _A' <- conv _A1 _A2
  (x, _B1, _B2) <- unbind2 bnd_B1 bnd_B2
  _B' <- extCtx x _A1 (conv _B1 _B2)
  return $ Pi i1 _A' (Bind x _B')
conv' (Form x1 _Is1) (Form x2 _Is2) | x1 == x2 =
  Form x1 <$> convArgs _Is1 _Is2
conv' (Form x1 _Is1) (Form x2 _Is2) | x1 /= x2 =
  throwGenErr $ "Type former names not equal"
   ++ show x1 ++ " != "  ++ show x2
conv' (Con x1 as1) (Con x2 as2) | x1 == x2 =
  Con x1 <$> convArgs as1 as2
conv' (Con x1 as1) (Con x2 as2) | x1 /= x2 =
  throwGenErr "Constructor names not equal"
conv' (Red x1 as1) (Red x2 as2) | x1 == x2 =
  Red x1 <$> convArgs as1 as2
conv' (Red x1 as1) (Red x2 as2) | x1 /= x2 =
  throwGenErr "Reduction names not equal"
conv' a1@(Meta x1 as1) a2 = millerPattern as1 >>= \case
  Just _As -> do
    solveMeta x1 (lams _As a2)
    return a2
  Nothing -> case a2 of
    Meta x2 as2 | x1 == x2 ->
      Meta x1 <$> convArgs as1 as2
    Meta x2 as2 | x1 /= x2 ->
      throwGenErr "Metavariable names not equal"
    otherwise -> throwErr (EConv a1 a2)
conv' a1 a2@(Meta _ _) = conv' a2 a1
conv' a b = throwErr (EConv a b)

convArg :: (Icit, Exp) -> (Icit, Exp) -> TCM (Icit, Exp)
convArg (i1, a1) (i2, a2) | i1 == i2 = (i1,) <$> conv a1 a2
convArg (i1, a1) (i2, a2) = throwGenErr "One argument is explicit and the other is implicit"

convArgs :: Args -> Args -> TCM Args
convArgs as1 as2 = mapM (uncurry convArg) (zip as1 as2)

----------------------------------------------------------------------

millerPattern :: Args -> TCM (Maybe Tel)
millerPattern as = (sequence <$> mapM varName as) >>= \case
  Just xs | length (names xs) == length (nub (names xs)) -> return (Just xs)
  otherwise -> return Nothing

varName :: (Icit, Exp) -> TCM (Maybe (Icit, Name, Exp))
varName (i, Var x) = lookupCtx x >>= \case
  Just _A -> return $ Just (i, x, _A)
  Nothing -> return Nothing
varName _ = return Nothing

----------------------------------------------------------------------
