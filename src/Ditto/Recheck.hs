module Ditto.Recheck where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Delta
import Ditto.Conv
import Ditto.Monad
import Ditto.Sub
import Ditto.Env
import Ditto.Match
import Ditto.Cover
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

reinferExtBind :: Exp -> Bind -> TCM Bind
reinferExtBind _A bnd_b = do
  (x, b) <- unbind bnd_b
  Bind x <$> extCtx x _A (reinfer b)

recheckExt :: Name -> Exp -> Exp -> Exp -> TCM ()
recheckExt x _A = recheckExts [(x, _A)]

recheckExts :: Tel -> Exp -> Exp -> TCM ()
recheckExts _As b _B = extCtxs _As (recheck b _B)

----------------------------------------------------------------------

recheck :: Exp -> Exp -> TCM ()
recheck a _A = do
  _A' <- reinfer a
  conv _A _A'
  return ()

reinfer :: Exp -> TCM Exp
reinfer (Var x) = lookupType x >>= \case
    Just _A -> return _A
    Nothing -> throwNotInScope x
reinfer Type = return Type
reinfer Infer = throwError "Core language does not reinfer expressions"
reinfer (Pi _A bnd_B) = do
  recheck _A Type
  (x, _B) <- unbind bnd_B
  recheckExt x _A _B Type
  return Type
reinfer (Lam _A b) = do
  recheck _A Type
  Pi _A <$> reinferExtBind _A b
reinfer (Form x is) = lookupPSigma x >>= \case
  Just (DForm _X _Is) -> do
    foldM_ recheckAndAdd [] (zip is _Is)
    return Type
  otherwise -> throwError $ "Not a type former name: " ++ show x
reinfer (Con x as) = lookupPSigma x >>= \case
  Just (DCon x _As _X _Is) -> do
    foldM_ recheckAndAdd [] (zip as _As)
    let s = zip (names _As) as
    _Is' <- mapM (flip sub s) _Is
    return $ Form _X _Is'
  otherwise -> throwError $ "Not a constructor name: " ++ show x
reinfer (Red x as) = lookupPSigma x >>= \case
  Just (DRed y cs _As _B) -> do
    foldM_ recheckAndAdd [] (zip as _As)
    sub _B (zip (names _As) as)
  otherwise -> throwError $ "Not a reduction name: " ++ show x
reinfer (Meta x as) = lookupMetaType x >>= \case
  Just (_As, _B) -> do
    foldM_ recheckAndAdd [] (zip as _As)
    sub _B (zip (names _As) as)
  Nothing -> throwError $ "Not a metavariable name: " ++ show x
reinfer (f :@: a) = reinfer f >>= whnf >>= \case
  Pi _A bnd_B -> do
    recheck a _A
    (x, _B) <- unbind bnd_B
    sub1 (x, a) _B
  otherwise -> throwError "Function does not have Pi type"

recheckAndAdd :: Sub -> (Exp, (Name, Exp)) -> TCM Sub
recheckAndAdd s (a , (x, _A))= do
  a' <- sub a s
  _A' <- sub _A s
  recheck a' _A'
  return $ (x, a'):s

----------------------------------------------------------------------
