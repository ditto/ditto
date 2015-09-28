module Ditto.Recheck where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Delta
import Ditto.Conv
import Ditto.Monad
import Ditto.Sub
import Ditto.Env
import Ditto.Pretty
import Data.Maybe
import Data.List
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative

----------------------------------------------------------------------

recheckDef :: (Name, Exp, Exp) -> TCM ()
recheckDef (x, a, _A) = do
  _A' <- whnf =<< deltaExpand _A
  a' <- whnf =<< deltaExpand a
  recheck a' _A'

recheckProg :: TCM ()
recheckProg = mapM_ recheckDef =<< lookupDefs

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
  conv _A _A'
  return ()

reinfer :: Exp -> TCM Exp
reinfer (Var x) = lookupType x >>= \case
    Just _A -> return _A
    Nothing -> throwErr (EScope x)
reinfer Type = return Type
reinfer (Infer _) = throwGenErr "Core language does not reinfer expressions"
reinfer (Pi i _A bnd_B) = do
  recheck _A Type
  (x, _B) <- unbind bnd_B
  recheckExt i x _A _B Type
  return Type
reinfer (Lam i _A b) = do
  recheck _A Type
  Pi i _A <$> reinferExtBind i _A b
reinfer (Form x is) = lookupPSigma x >>= \case
  Just (DForm _X _Is) -> do
    foldM_ recheckAndAdd [] (zip is _Is)
    return Type
  otherwise -> throwGenErr $ "Not a type former name: " ++ show x
reinfer (Con x as) = lookupPSigma x >>= \case
  Just (DCon x _As _X _Is) -> do
    foldM_ recheckAndAdd [] (zip as _As)
    let s = mkSub _As as
    _Is' <- subs _Is s
    return $ Form _X _Is'
  otherwise -> throwGenErr $ "Not a constructor name: " ++ show x
reinfer (Red x as) = lookupPSigma x >>= \case
  Just (DRed y cs _As _B) -> do
    foldM_ recheckAndAdd [] (zip as _As)
    sub _B (mkSub _As as)
  otherwise -> throwGenErr $ "Not a reduction name: " ++ show x
reinfer (Meta x as) = lookupMetaType x >>= \case
  Just (_As, _B) -> do
    foldM_ recheckAndAdd [] (zip as _As)
    sub _B (mkSub _As as)
  Nothing -> throwGenErr $ "Not a metavariable name: " ++ show x
reinfer (App i1 f a) = reinfer f >>= whnf >>= \case
  Pi i2 _A bnd_B | i1 == i2 -> do
    recheck a _A
    (x, _B) <- unbind bnd_B
    sub1 (x, a) _B
  otherwise -> throwGenErr "Function does not have Pi type"

recheckAndAdd :: Sub -> ((Icit, Exp), (Icit, Name, Exp)) -> TCM Sub
recheckAndAdd s ((i1, a) , (i2, x, _A)) | i1 == i2 = do
  a' <- sub a s
  _A' <- sub _A s
  recheck a' _A'
  return $ (x, a'):s
recheckAndAdd s ((i1, a) , (i2, x, _A)) = do
  throwGenErr "Implicit and explicit application mismatch"

----------------------------------------------------------------------
