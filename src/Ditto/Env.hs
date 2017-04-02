module Ditto.Env where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Throw
import Data.List
import Control.Monad.State

----------------------------------------------------------------------

genMetaPi :: Tel -> Icit -> TCM Exp
genMetaPi _As i = do
  acts <- getActs
  _X <- addMeta MInfer acts _As EType
  let _A = EMeta _X (varArgs _As)
  x <- gensymInacc
  let _Bs = snoc _As (i, x, _A)
  _Y <- addMeta MInfer acts _Bs EType
  let _B = EMeta _Y (varArgs _Bs)
  return (EPi i _A (Bind x _B))

genMeta :: MKind -> TCM (Exp, Exp)
genMeta m = do
  acts <- getActs
  _As <- getCtx
  _X <- addMeta MInfer acts _As EType
  let _B = EMeta _X (varArgs _As)
  x <- addMeta m acts _As _B
  let b = EMeta x (varArgs _As)
  return (b, _B)

addMeta :: MKind -> Acts -> Tel -> Exp -> TCM MName
addMeta k acts ctx _A = do
  x <- gensymMeta k
  insertMeta x acts ctx _A
  return x

solveMeta :: MName -> Exp -> TCM ()
solveMeta x a = insertSol x a

----------------------------------------------------------------------

ensureUniqName :: Name -> TCM ()
ensureUniqName x = do
  xs <- allNames
  when (elem x xs) $ throwGenErr
    $ "Definition name already exists in the environment: " ++ show x

ensureUniqPName :: PName -> TCM ()
ensureUniqPName x = do
  xs <- allPNames
  when (elem x xs) $ throwGenErr
    $ "Primitive name already exists in the environment: " ++ show x

----------------------------------------------------------------------

addDef :: Name -> Exp -> Exp -> TCM ()
addDef x a _A = do
  ensureUniqName x
  insertDef x a _A

genGuard :: Exp -> Exp -> Prob -> TCM Exp
genGuard a _A p = do
  _As <- getCtx
  x <- gensymGuard
  insertProb x p
  insertGuard x (lams _As a) (pis _As _A)
  return $ apps (EGuard x) (varArgs _As)

----------------------------------------------------------------------

addForm :: PName -> Tel -> TCM ()
addForm x _Is = do
  ensureUniqPName x
  insertForm x _Is
  addDef (pname2name x) (lams _Is (EForm x (varArgs _Is))) (formType _Is)
  insertCrumb (CData x)

addCon :: (PName, Tel, PName, Args) -> TCM ()
addCon (x, _As, _X, _Is) = do
  ensureUniqPName x
  insertCon _X (x, Con _As _Is)
  addDef (pname2name x) (lams _As (ECon _X x (varArgs _As))) (conType _As _X _Is)

----------------------------------------------------------------------

addRed :: PName -> Tel -> Exp -> TCM ()
addRed x _As _B = do
  ensureUniqPName x
  insertRed x _As _B
  addDef (pname2name x) (lams _As (ERed x (varArgs _As))) (pis _As _B)
  insertCrumb (CDefn x)

addClauses :: PName -> Clauses -> TCM ()
addClauses x cs = insertClauses x cs

----------------------------------------------------------------------
