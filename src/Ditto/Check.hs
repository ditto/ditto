{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Ditto.Check where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Conv
import Ditto.Monad
import Ditto.Sub
import Ditto.Match
import Ditto.Cover
import Data.Maybe
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
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
      mapM_ (\c -> addCon =<< buildCon x c) cs
    otherwise -> throwError "Datatype former does not end in Type"
checkStmt (SDefn x _A cs) = do
  check _A Type
  (_As, _B) <- splitTel _A
  cs' <- cover cs _As (pvarNames _As)
  let unreached = unreachableClauses cs cs'
  unless (null unreached) $ do
    throwError $ "Unreachable user clauses:\n"
      ++ (unlines (map show unreached))
      ++ "\nCovered by:\n"
      ++ (unlines (map show cs'))
  addRed x cs' _As _B
  mapM_ (\(_Delta, lhs, rhs) -> checkRHS _Delta lhs rhs _As _B) cs'

checkRHS :: Tel -> [Pat] -> Exp -> Tel -> Exp -> TCM ()
checkRHS _Delta lhs rhs _As _B
  = checkExts _Delta rhs =<< subClauseType _B _As lhs

----------------------------------------------------------------------

inferExt :: (Name, Exp) -> Exp -> TCM Exp
inferExt (x , _A) b = local (extCtx x _A) (infer b)

checkExt :: (Name, Exp) -> Exp -> Exp -> TCM ()
checkExt _A b _B = checkExts [_A] b _B

checkExts :: Tel -> Exp -> Exp -> TCM ()
checkExts _As b _B = local (extCtxs _As) (check b _B)

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
    Nothing -> do
      DittoR {ctx = ctx} <- ask
      DittoS {sig = sig} <- get
      throwError $ "Variable not in scope: " ++ show x
        ++ "\nContext:\n"
        ++ unlines (map show ctx)
        ++ "\nEnvironment:\n"
        ++ unlines (map show sig)
infer Type = return Type
infer (Pi x _A _B) = do
  check _A Type
  checkExt (x , _A) _B Type
  return Type
infer (Lam x _A b) = do
  _B <- inferExt (x, _A) b
  return $ Pi x _A _B
infer (Form x is) = error "infer type former not implemented"
infer (Con x as) = do
  _C <- lookupPSigma x
  case _C of
   Just (DCon x _As _X _Is) -> do
     mapM (uncurry check) (zip as (types _As))
     let sigma :: Sub = zip (names _As) as
     _Is' <- mapM (\a -> sub a sigma) _Is
     return $ Form _X _Is'
   otherwise -> throwError $ "Not a constructor name: " ++ show x
infer (Red x as) = error "infer reduction not implemented"
infer (f :@: a) = do
  _AB <- infer f
  case _AB of
    Pi x _A _B -> do
      check a _A
      sub1 (x, a) _B
    otherwise -> throwError "Function does not have Pi type"

----------------------------------------------------------------------
