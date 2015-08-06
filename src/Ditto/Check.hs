module Ditto.Check where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Conv
import Ditto.Monad
import Ditto.Sub
import Control.Monad.Except
import Control.Monad.Reader

inferExt :: (Name, Exp) -> Exp -> TCM Exp
inferExt (x , _A) b = local (extCtx x _A) (infer b)

checkExt :: (Name, Exp) -> Exp -> Exp -> TCM ()
checkExt (x , _A) b _B = local (extCtx x _A) (check b _B)

check :: Exp -> Exp -> TCM ()
check a _A = do
  _A' <- infer a
  conv _A _A'
  return ()

infer :: Exp -> TCM Exp
infer (EVar x) = do
  ma <- lookupType x
  case ma of
    Just _A -> return _A
    Nothing -> throwError "Variable not in scope"
infer Type = return Type
infer (Pi x _A _B) = do
  check _A Type
  checkExt (x , _A) _B Type
  return Type  
infer (Lam x _A b) = do
  _B <- inferExt (x, _A) b
  return $ Pi x _A _B
infer (f :@: a) = do
  _AB <- infer f
  case _AB of
    Pi x _A _B -> do
      check a _A
      return (sub (x, a) _B)
    otherwise -> throwError "Function does not have Pi type"

