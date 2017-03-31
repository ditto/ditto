module Ditto.Conv where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Expand
import Ditto.Monad
import Ditto.Sub
import Ditto.Env
import Ditto.Throw
import Data.List

----------------------------------------------------------------------

alpha :: Exp -> Exp -> Bool
alpha a b = alpha' [] a b

alpha' :: Ren -> Exp -> Exp -> Bool
alpha' dict EType EType = True
alpha' dict (EInfer _) (EInfer _) = False
alpha' dict (EForm x1 as1) (EForm x2 as2) =
  x1 == x2 && alphas' dict as1 as2
alpha' dict (ECon x1 as1) (ECon x2 as2) =
  x1 == x2 && alphas' dict as1 as2
alpha' dict (ERed x1 as1) (ERed x2 as2) =
  x1 == x2 && alphas' dict as1 as2
alpha' dict (EMeta x1 as1) (EMeta x2 as2) =
  x1 == x2 && alphas' dict as1 as2
alpha' dict (EGuard x1) (EGuard x2) = x1 == x2
alpha' dict (EVar x) (EVar y) =
  case lookup x dict of
    Nothing -> x == y
    Just x' -> x' == y
alpha' dict (ELam i1 _A1 (Bind x a1)) (ELam i2 _A2 (Bind y a2)) =
  i1 == i2 && alpha' dict' _A1 _A2 && alpha' dict' a1 a2
    where dict' = (x, y) : dict
alpha' dict (EPi i1 _A1 (Bind x _B1)) (EPi i2 _A2 (Bind y _B2)) =
  i1 == i2 && alpha' dict' _A1 _A2 && alpha' dict' _B1 _B2
    where dict' = (x, y) : dict
alpha' dict (EApp i1 f1 a1) (EApp i2 f2 a2) =
  i1 == i2 && alpha' dict f1 f2 && alpha' dict a1 a2
alpha' dict _ _ = False

alphas' :: Ren -> Args -> Args -> Bool
alphas' dict as1 as2 = all
  (\((i1, a1) , (i2, a2)) -> i1 == i2 && alpha' dict a1 a2)
  (zip as1 as2)

----------------------------------------------------------------------

convStatic :: a -> Exp -> Exp -> TCM a
convStatic ret a1 a2 = conv a1 a2 >>= \case
  Nothing -> return ret
  Just p -> throwProbErr p

----------------------------------------------------------------------

conv :: Exp -> Exp -> TCM MProb
conv a b = during (AConv a b) (convActless a b)

convActless :: Exp -> Exp -> TCM MProb
convActless a b = if alpha a b
  then return Nothing
  else do
    a' <- whnf a
    b' <- whnf b
    conv' a' b'

conv' :: Exp -> Exp -> TCM MProb

conv' EType EType = return Nothing
conv' (EInfer _) (EInfer _) = throwGenErr "Unelaborated metavariables are unique"
conv' (ELam i1 _A1 bnd_b1) (ELam i2 _A2 bnd_b2) | i1 == i2 = do
  (x, b1, b2) <- unbind2 bnd_b1 bnd_b2
  extCtx i1 x _A1 (conv b1 b2)
conv' (EPi i1 _A1 bnd_B1) (EPi i2 _A2 bnd_B2) | i1 == i2 = do
  (x, _B1, _B2) <- unbind2 bnd_B1 bnd_B2
  conv _A1 _A2 >>= \case
    Nothing -> extCtx i1 x _A1 (conv _B1 _B2)
    Just p -> extCtx i1 x _A1 (Just <$> mkProbN p (f _B1) (f _B2))
  where f a = [(Expl, a)]
conv' (EForm x1 _Is1) (EForm x2 _Is2) | x1 == x2 =
  convArgs _Is1 _Is2
conv' (ECon x1 as1) (ECon x2 as2) | x1 == x2 =
  convArgs as1 as2

-- Function Eta Expansion
conv' f1@(ELam i _A bnd_b) f2 = do
  (x , _) <- unbind bnd_b
  conv' f1 (ELam i _A (Bind x (EApp i f2 (EVar x))))
conv' f1 f2@(ELam _ _ _) = conv' f2 f1

-- Reducible terms / Spines

conv' (viewSpine -> (EVar x1, as1)) (viewSpine -> (EVar x2, as2)) | x1 == x2 =
  convArgs as1 as2
conv' (viewSpine -> (ERed x1 as1, bs1)) (viewSpine -> (ERed x2 as2, bs2)) | x1 == x2 =
  convArgs (as1 ++ bs1) (as2 ++ bs2)

conv' a1@(viewSpine -> (EGuard x1, bs1)) a2 = Just <$> mkProb1 a1 a2
conv' a1 a2@(viewSpine -> (EGuard _, _)) = conv' a2 a1

-- Solving Metavariables
conv' (viewSpine -> (EMeta x1 as1, bs1)) a2 = do
  as1 <- expands metaForm as1
  as2 <- expands metaForm bs1
  a2 <- expand metaForm a2

  millerPattern x1 (as1 ++ bs1) a2 >>= \case
    Just _As -> do
      solveMeta x1 (lams _As a2)
      return Nothing
    Nothing -> let a1 = apps (EMeta x1 as1) bs1
      in Just <$> mkProb1 a1 a2
     
conv' a1 a2@(viewSpine -> (EMeta _ _, _)) = conv' a2 a1

conv' a b = throwConvErr a b

----------------------------------------------------------------------

convArg :: (Icit, Exp) -> (Icit, Exp) -> TCM MProb
convArg (i1, a1) (i2, a2) | i1 == i2 = conv a1 a2
convArg (i1, a1) (i2, a2) = throwGenErr "One argument is explicit and the other is implicit"

convArgs :: Args -> Args -> TCM MProb
convArgs [] [] = return Nothing
convArgs (a1:as1) (a2:as2) = convArg a1 a2 >>= \case
  Nothing -> convArgs as1 as2
  Just p -> Just <$> mkProbN p as1 as2
convArgs as1 as2 = throwGenErr "Converting arguments of differing lengths"

----------------------------------------------------------------------

millerPattern :: MName -> Args -> Exp -> TCM (Maybe Tel)
millerPattern x as a = (sequence <$> mapM varName as) >>= \case
  Just _As | linearNames _As && flexInScope x a -> solInScope _As a
  otherwise -> return Nothing

linearNames :: Tel -> Bool
linearNames _As = length (names _As) == length (nub (names _As))

createdAt :: Flex -> Integer
createdAt (Left (MName _ n)) = n
createdAt (Right (GName n)) = n

flexInScope :: MName -> Exp -> Bool
flexInScope (Left -> x) (mv -> ys) = all (\y -> createdAt y < createdAt x) ys

solInScope :: Tel -> Exp -> TCM (Maybe Tel)
solInScope _As a = do
  xs <- fvCtx a
  if all (flip elem (names _As)) xs
  then return (Just _As)
  else return Nothing

varName :: (Icit, Exp) -> TCM (Maybe (Icit, Name, Exp))
varName (i, EVar x) = lookupCtx x >>= \case
  Just _A -> return $ Just (i, x, _A)
  Nothing -> return Nothing
varName _ = return Nothing

----------------------------------------------------------------------
