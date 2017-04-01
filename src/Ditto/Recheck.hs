module Ditto.Recheck where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Ditto.Whnf
import Ditto.Expand
import Ditto.Surf
import Ditto.Conv
import Ditto.Throw
import Control.Monad.State

----------------------------------------------------------------------

recheckDef :: (Name, Ann) -> TCM ()
recheckDef (x, Ann a _A) = do
  _A' <- whnf =<< expand deltaForm _A
  a' <- whnf =<< expand deltaForm a
  recheck a' _A'

recheckProg :: TCM ()
recheckProg = mapM_ recheckDef =<< allDefs

----------------------------------------------------------------------

reinferExtBind :: Icit -> Exp -> Bind -> TCM Bind
reinferExtBind i _A bnd_b = do
  (x, b) <- unbind bnd_b
  Bind x <$> extCtx i x _A (reinfer b)

recheckExt :: Icit -> Name -> Exp -> Exp -> Exp -> TCM ()
recheckExt i x _A b _B = extCtx i x _A (recheck b _B)

----------------------------------------------------------------------

recheck :: Exp -> Exp -> TCM ()
recheck a _A = do
  _A' <- reinfer a
  convStatic () _A _A'
  return ()

reinfer :: Exp -> TCM Exp
reinfer (EVar x) = lookupType x >>= \case
    Just _A -> return _A
    Nothing -> throwScopeErr x
reinfer EType = return EType
reinfer (EPi i _A bnd_B) = do
  recheck _A EType
  (x, _B) <- unbind bnd_B
  recheckExt i x _A _B EType
  return EType
reinfer (ELam i _A b) = do
  recheck _A EType
  EPi i _A <$> reinferExtBind i _A b
reinfer (EForm x is) = lookupPSigma x >>= \case
  Just (DForm _X _ _Is) -> do
    foldM_ recheckAndAdd [] (zip is _Is)
    return EType
  otherwise -> throwGenErr $ "Not a type former name: " ++ show x
reinfer (ECon x as) = lookupCon undefined x >>= \case
  Just (_X, Con _As is) -> do
    foldM_ recheckAndAdd [] (zip as _As)
    let s = mkSub _As as
    is' <- subs is s
    return $ EForm _X is'
  otherwise -> throwGenErr $ "Not a constructor name: " ++ show x
reinfer (ERed x as) = lookupRed x >>= \case
  Just (Red _As _B) -> do
    cs <- lookupClauses x
    foldM_ recheckAndAdd [] (zip as _As)
    sub _B (mkSub _As as)
  otherwise -> throwGenErr $ "Not a reduction name: " ++ show x
reinfer (EApp i1 f a) = reinfer f >>= whnf >>= \case
  EPi i2 _A bnd_B | i1 == i2 -> do
    recheck a _A
    (x, _B) <- unbind bnd_B
    sub1 (x, a) _B
  otherwise -> throwGenErr "Function does not have Pi type"
reinfer x = throwGenErr ("Reinfer of a non-core term: " ++ show x)

recheckAndAdd :: Sub -> ((Icit, Exp), (Icit, Name, Exp)) -> TCM Sub
recheckAndAdd s ((i1, a) , (i2, x, _A)) | i1 == i2 = do
  a' <- sub a s
  _A' <- sub _A s
  recheck a' _A'
  return $ (x, a'):s
recheckAndAdd s ((i1, a) , (i2, x, _A)) = do
  throwGenErr "Implicit and explicit application mismatch"

----------------------------------------------------------------------
