module Ditto.Check where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Conv
import Ditto.Monad
import Ditto.Sub
import Control.Monad.Except
import Control.Monad.Reader
import Control.Applicative

----------------------------------------------------------------------

runCheck :: Exp -> Exp -> Either String ()
runCheck a _A = runTCM (check a _A)

runCheckProg :: [Stmt] -> Either String ()
runCheckProg = runTCM . checkProg

----------------------------------------------------------------------

checkProg :: [Stmt] -> TCM ()
checkProg = mapM_ checkStmt

checkStmt :: Stmt -> TCM ()
checkStmt (SDef x a _A) = do
  check a _A
  addDef x a _A
checkStmt (SData x _A cs) = do
  check _A Type
  (tel, end) <- splitTel _A
  case end of
    Type -> do
      addForm x tel
      mapM_ (\ (_, _A) -> check _A Type) cs
      mapM_ (\c -> addSig =<< buildCon x c) cs
    otherwise -> throwError "Datatype former does not end in Type"

----------------------------------------------------------------------

inferExt :: (Name, Exp) -> Exp -> TCM Exp
inferExt (x , _A) b = local (extCtx x _A) (infer b)

checkExt :: (Name, Exp) -> Exp -> Exp -> TCM ()
checkExt (x , _A) b _B = local (extCtx x _A) (check b _B)

----------------------------------------------------------------------

check :: Exp -> Exp -> TCM ()
check a _A = do
  _A' <- infer a
  conv _A _A'
  return ()

infer :: Exp -> TCM Exp
infer (Var x) = do
  ma <- lookupCtx x
  case ma of
    Just _A -> return _A
    Nothing -> throwError $ "Variable not in scope: " ++ x
infer Type = return Type
infer (Pi x _A _B) = do
  check _A Type
  checkExt (x , _A) _B Type
  return Type
infer (Lam x _A b) = do
  _B <- inferExt (x, _A) b
  return $ Pi x _A _B
infer (Form x is) = error "infer type former not implemented"
infer (Con x as) = error "infer constructor former not implemented"
infer (f :@: a) = do
  _AB <- infer f
  case _AB of
    Pi x _A _B -> do
      check a _A
      sub (x, a) _B
    otherwise -> throwError "Function does not have Pi type"

----------------------------------------------------------------------
