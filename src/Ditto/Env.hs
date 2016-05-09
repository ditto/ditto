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

genMeta :: MKind -> TCM (Exp, Exp)
genMeta m = do
  _As <- getCtx
  _X <- addMeta MInfer _As Type
  let _B = Meta _X (varArgs _As)
  x <- addMeta m _As _B
  let b = Meta x (varArgs _As)
  return (b, _B)

addMeta :: MKind -> Tel -> Exp -> TCM MName
addMeta k _As _B = do
  x <- gensymMeta k
  addSig (DMeta x Nothing _As _B)
  return x

solveMeta :: MName -> Exp -> TCM ()
solveMeta x a = do
  env <- getEnv
  case find (isMNamed x) env of
    Just s@(DMeta _ Nothing _As _B) -> do
      updateSig s (DMeta x (Just a) _As _B)
    Just s@(DMeta _ _ _ _) -> throwGenErr $
      "Metavariable is already defined: " ++ show x
    _ -> throwGenErr $
      "Metavariable does not exist in the environment: " ++ show x

----------------------------------------------------------------------

addForm :: PName -> Tel -> TCM ()
addForm x _Is = do
  env <- getEnv
  when (any (isPNamed x) env) $ throwGenErr
    $ "Type former name already exists in the environment: " ++ show x
  addSig (DForm x [] _Is)
  addDef (pname2name x) (Just (lams _Is (Form x (varArgs _Is)))) (formType _Is)

addCon :: (PName, Tel, PName, Args) -> TCM ()
addCon (x, _As, _X, _Is) = do
  env <- getEnv
  when (any (isPNamed x) env) $ throwGenErr
    $ "Constructor name already exists in the environment: " ++ show x
  case find (isPNamed _X) env of
      Just s@(DForm _ cs _Js) -> do
        updateSig s (DForm _X (snoc cs (x, _As, _Is)) _Js)
        addDef (pname2name x) (Just (lams _As (Con x (varArgs _As)))) (conType _As _X _Is)
      _ -> throwGenErr $
        "Datatype does not exist in the environment: " ++ show _X

addRedType :: PName -> Tel -> Exp -> TCM ()
addRedType x _As _B = do
  env <- getEnv
  when (any (isPNamed x) env) $ throwGenErr
    $ "Reduction name already exists in the environment: " ++ show x
  addSig (DRed x [] _As _B)
  addDef (pname2name x) (Just (lams _As (Red x (varArgs _As)))) (pis _As _B)

addRedClauses :: PName -> [CheckedClause] -> TCM ()
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
