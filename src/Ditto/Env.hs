module Ditto.Env where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.Except

----------------------------------------------------------------------

addSig :: Sigma -> TCM ()
addSig s = do
  state@DittoS {sig = sig} <- get
  when (s `elem` sig) $ throwError $
    "Element being added already exists in the environment: " ++ show s
  put state { sig = s : sig }

updateSig :: Sigma -> Sigma -> TCM ()
updateSig s s' = do
  state@DittoS {sig = sig} <- get
  case break (== s) sig of
    (sig1, _:sig2) -> put state { sig = sig1 ++ s':sig2 }
    (sig1, []) -> throwError $
      "Element being updated does not exist in the environment: " ++ show s

addDef :: Name -> Exp -> Exp -> TCM ()
addDef x a _A = do
  DittoS {sig = sig} <- get
  when (any (isNamed x) sig) $ throwError
    $ "Definition name already exists in the environment: " ++ show x
  addSig (Def x a _A)

addForm :: PName -> Tel -> TCM ()
addForm x _Is = do
  DittoS {sig = sig} <- get
  when (any (isPNamed x) sig) $ throwError
    $ "Type former name already exists in the environment: " ++ show x
  addSig (DForm x _Is)
  _Is' <- freshenShadows _Is
  addDef (pname2name x) (lams _Is' (Form x (varNames _Is'))) (formType _Is)

addCon :: (PName, Tel, PName, [Exp]) -> TCM ()
addCon (x, _As, _X, _Is) = do
  DittoS {sig = sig} <- get
  when (any (isPNamed x) sig) $ throwError
    $ "Constructor name already exists in the environment: " ++ show x
  addSig (DCon x _As _X _Is)
  _As' <- freshenShadows _As
  addDef (pname2name x) (lams _As' (Con x (varNames _As'))) (pis _As $ Form _X _Is)

addRedType :: PName -> Tel -> Exp -> TCM ()
addRedType x _As _B = do
  DittoS {sig = sig} <- get
  when (any (isPNamed x) sig) $ throwError
    $ "Reduction name already exists in the environment: " ++ show x
  addSig (DRed x [] _As _B)
  _As' <- freshenShadows _As
  addDef (pname2name x) (lams _As' (Red x (varNames _As'))) (pis _As _B)

addRedClauses :: PName -> [CheckedClause] -> TCM ()
addRedClauses x cs = do
  DittoS {sig = sig} <- get
  case find (isPNamed x) sig of
    Just s@(DRed _ [] _As _B) -> do
      updateSig s (DRed x cs _As _B)
    Just s@(DRed _ _ _As _B) -> throwError $
      "Reduction already contains clauses: " ++ show x
    _ -> throwError $
      "Reduction does not exist in the environment: " ++ show x

----------------------------------------------------------------------
