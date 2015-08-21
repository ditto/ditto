{-# LANGUAGE TupleSections, LambdaCase #-}

module Ditto.Check where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Delta
import Ditto.Conv
import Ditto.Monad
import Ditto.Sub
import Ditto.Env
import Ditto.Match
import Ditto.Cover
import Data.Maybe
import Data.List
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative

----------------------------------------------------------------------

runCheck :: Exp -> Exp -> Either String ()
runCheck a _A = runTCM (check a _A)

runCheckProg :: [Stmt] -> Either String ()
runCheckProg = runTCM . checkProg

runCheckProgDelta :: [Stmt] -> Either String ()
runCheckProgDelta xs = runTCM (checkProg xs >> checkProgDelta)

----------------------------------------------------------------------

checkDelta :: (Name, Exp, Exp) -> TCM ()
checkDelta (x, a, _A) = do
  _A' <- whnf =<< deltaExpand _A
  a' <- whnf =<< deltaExpand a
  check a' _A'

checkProgDelta :: TCM ()
checkProgDelta = mapM_ checkDelta =<< lookupDefs

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
      mapM_ (\ (_, _A') -> check _A' Type) cs
      mapM_ (\c -> addCon =<< buildCon x c) cs
    otherwise -> throwError "Datatype former does not end in Type"
checkStmt (SDefn x _A cs) = do
  cs <- atomizeClauses cs
  checkLinearClauses x cs
  check _A Type
  (_As, _B) <- splitTel _A
  addRedType x _As _B
  cs' <- cover cs _As
  let unreached = unreachableClauses cs cs'
  unless (null unreached) $ do
    throwError $ "Unreachable user clauses:\n"
      ++ (unlines (map show unreached))
      ++ "\nCovered by:\n"
      ++ (unlines (map show cs'))
  mapM_ (\(_Delta, lhs, rhs) -> checkRHS _Delta lhs rhs _As _B) cs'
  addRedClauses x cs'

----------------------------------------------------------------------

checkRHS :: Tel -> [Pat] -> Exp -> Tel -> Exp -> TCM ()
checkRHS _Delta lhs rhs _As _B
  = checkExts _Delta rhs =<< subClauseType _B _As lhs

----------------------------------------------------------------------

checkLinearClauses :: PName -> [Clause] -> TCM ()
checkLinearClauses x = mapM_ (checkLinearClause x)

checkLinearClause :: PName -> Clause -> TCM ()
checkLinearClause x (ps, rhs) =
  unless (null xs) $ throwError $
    unlines ["Nonlinear occurrence of variables in patterns."
            , "Variables: " ++ show xs
            , "Function: " ++ show x
            , "Patterns: " ++ show ps
            ]
  where xs = nonLinearVars ps

nonLinearVars :: [Pat] -> [Name]
nonLinearVars ps = xs \\ nub xs
  where xs = patternsVars ps

patternsVars :: [Pat] -> [Name]
patternsVars = concat . map patternVars

patternVars :: Pat -> [Name]
patternVars (PVar x) = [x]
patternVars (Inacc _) = []
patternVars (PCon _ ps) = patternsVars ps

----------------------------------------------------------------------

atomizeClauses :: [Clause] -> TCM [Clause]
atomizeClauses = mapM (\(ps, rhs) -> (,rhs) <$> atomizePatterns ps)

atomizePatterns :: [Pat] -> TCM [Pat]
atomizePatterns = mapM atomizePattern

atomizePattern :: Pat -> TCM Pat
atomizePattern (PVar x) = case name2pname x of
  Just x' -> lookupPSigma x' >>= \case
    Just (DCon _ [] _ _) -> return $ PCon x' []
    otherwise -> return $ PVar x
  Nothing -> return $ PVar x
atomizePattern (PCon x ps) = PCon x <$> atomizePatterns ps
atomizePattern x@(Inacc _) = return x

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
infer (Form x is) = do
  lookupPSigma x >>= \case
    Just (DForm _X _Is) -> do
      foldM_ checkAndAdd [] (zip is _Is)
      return Type
    otherwise -> throwError $ "Not a type former name: " ++ show x
infer (Con x as) = do
  lookupPSigma x >>= \case
   Just (DCon x _As _X _Is) -> do
     foldM_ checkAndAdd [] (zip as _As)
     let s = zip (names _As) as
     _Is' <- mapM (flip sub s) _Is
     return $ Form _X _Is'
   otherwise -> throwError $ "Not a constructor name: " ++ show x
infer (Red x as) = do
  lookupPSigma x >>= \case
    Just (DRed y cs _As _B) -> do
      foldM_ checkAndAdd [] (zip as _As)
      sub _B (zip (names _As) as)
    otherwise -> throwError $ "Not a reduction name: " ++ show x
infer (f :@: a) = do
  _AB <- infer f
  case _AB of
    Pi x _A _B -> do
      check a _A
      sub1 (x, a) _B
    otherwise -> throwError "Function does not have Pi type"

checkAndAdd :: Sub -> (Exp, (Name, Exp)) -> TCM Sub
checkAndAdd s (a , (x, _A))= do
  a' <- sub a s
  _A' <- sub _A s
  check a' _A'
  return $ (x, a'):s

----------------------------------------------------------------------
