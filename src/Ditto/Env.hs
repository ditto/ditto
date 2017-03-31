module Ditto.Env where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Throw
import Data.List
import Control.Monad.State

----------------------------------------------------------------------

addSig :: Sigma -> TCM ()
addSig s = do
  state@DittoS {env = env} <- get
  when (s `elem` env) $ throwGenErr $
    "Element being added already exists in the environment: " ++ show s
  put state { env = snoc env s }

updateSig :: Sigma -> Sigma -> TCM ()
updateSig s s' = do
  state@DittoS {env = env} <- get
  case break (== s) env of
    (env1, _:env2) -> put state { env = env1 ++ s':env2 }
    (env1, []) -> throwGenErr $
      "Element being updated does not exist in the environment: " ++ show s

addDef :: Name -> Maybe Exp -> Exp -> TCM ()
addDef x a _A = do
  env <- getEnv
  when (any (isNamed x) env) $ throwGenErr
    $ "Definition name already exists in the environment: " ++ show x
  addSig (Def x a _A)

updateDef :: Name -> Exp -> TCM ()
updateDef x a = do
  env <- getEnv
  case find (isNamed x) env of
      Just s@(Def _ _ _A) -> updateSig s (Def x (Just a) _A)
      _ -> throwGenErr $
        "Definition does not exist in the environment: " ++ show x

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
  addSig (DMeta x Nothing acts ctx _A)
  return x

solveMeta :: MName -> Exp -> TCM ()
solveMeta x a = do
  env <- getEnv
  case find (isMNamed x) env of
    Just s@(DMeta _ Nothing acts ctx _A) -> do
      updateSig s (DMeta x (Just a) acts ctx _A)
    Just s@(DMeta _ _ _ _ _) -> throwGenErr $
      "Metavariable is already defined: " ++ show x
    _ -> throwGenErr $
      "Metavariable does not exist in the environment: " ++ show x

----------------------------------------------------------------------

genGuard :: Exp -> Exp -> Prob -> TCM Exp
genGuard a _A p = do
  _As <- getCtx
  x <- gensymGuard
  insertProb x p
  addSig (DGuard x (lams _As a) (pis _As _A))
  return $ apps (EGuard x) (varArgs _As)

----------------------------------------------------------------------

addForm :: PName -> Tel -> TCM ()
addForm x _Is = do
  env <- getEnv
  when (any (isPNamed x) env) $ throwGenErr
    $ "Type former name already exists in the environment: " ++ show x
  addSig (DForm x [] _Is)
  addDef (pname2name x) (Just (lams _Is (EForm x (varArgs _Is)))) (formType _Is)

addCon :: (PName, Tel, PName, Args) -> TCM ()
addCon (x, _As, _X, _Is) = do
  env <- getEnv
  when (any (isPNamed x) env) $ throwGenErr
    $ "Constructor name already exists in the environment: " ++ show x
  case find (isPNamed _X) env of
      Just s@(DForm _ cs _Js) -> do
        updateSig s (DForm _X (snoc cs (x, _As, _Is)) _Js)
        addDef (pname2name x) (Just (lams _As (ECon x (varArgs _As)))) (conType _As _X _Is)
      _ -> throwGenErr $
        "Datatype does not exist in the environment: " ++ show _X

addRedType :: PName -> Tel -> Exp -> TCM ()
addRedType x _As _B = do
  env <- getEnv
  when (any (isPNamed x) env) $ throwGenErr
    $ "Reduction name already exists in the environment: " ++ show x
  addSig (DRed x [] _As _B)
  addDef (pname2name x) (Just (lams _As (ERed x (varArgs _As)))) (pis _As _B)

addRedClauses :: PName -> Clauses -> TCM ()
addRedClauses x cs = do
  env <- getEnv
  case find (isPNamed x) env of
    Just s@(DRed _ [] _As _B) -> do
      updateSig s (DRed x cs _As _B)
    Just s@(DRed _ _ _As _B) -> throwGenErr $
      "Reduction already contains clauses: " ++ show x
    _ -> throwGenErr $
      "Reduction does not exist in the environment: " ++ show x

----------------------------------------------------------------------
