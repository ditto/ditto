module Ditto.Check where
import Ditto.Syntax
import Ditto.Whnf
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

runCheckProg :: Verbosity -> [Stmt] -> Either String ()
runCheckProg v = runTCM v . checkProg

----------------------------------------------------------------------

checkProg :: [Stmt] -> TCM ()
checkProg ds = mapM_ checkStmt ds

checkStmt :: Stmt -> TCM ()
checkStmt (SDef x a _A) = do
  _A <- checkSolved _A Type
  a  <- checkSolved a _A
  addDef x a _A
checkStmt (SData x _A cs) = do
  _A <- checkSolved _A Type
  (tel, end) <- splitTel _A
  case end of
    Type -> do
      addForm x tel
      cs <- mapM (\ (x, _A') -> (x,) <$> checkSolved _A' Type) cs
      mapM_ (\c -> addCon =<< buildCon x c) cs
    otherwise -> throwError "Datatype former does not end in Type"
checkStmt (SDefn x _A cs) = do
  cs <- atomizeClauses cs
  checkLinearClauses x cs
  _A <- checkSolved _A Type
  (_As, _B) <- splitTel _A
  addRedType x _As _B
  cs' <- cover cs _As
  let unreached = unreachableClauses cs cs'
  unless (null unreached) $ throwError
      $ "Unreachable user clauses:\n"
      ++ (unlines (map show unreached))
      ++ "\nCovered by:\n"
      ++ (unlines (map show cs'))
  addRedClauses x =<< mapM (\(_Delta, lhs, rhs) -> (_Delta, lhs,) <$> checkRHS _Delta lhs rhs _As _B) cs'

----------------------------------------------------------------------

checkRHS :: Ctx -> Pats -> RHS -> Tel -> Exp -> TCM RHS
checkRHS _Delta lhs (Prog a) _As _B
  = Prog <$> (checkExtsSolved _Delta a =<< subClauseType _B _As lhs)
checkRHS _Delta lhs (Caseless x) _As _B = split (toTel _Delta) x >>= \case
    [] -> return (Caseless x)
    otherwise -> throwError $ "Variable is not caseless: " ++ show x

----------------------------------------------------------------------

checkLinearClauses :: PName -> [Clause] -> TCM ()
checkLinearClauses x = mapM_ (checkLinearClause x)

checkLinearClause :: PName -> Clause -> TCM ()
checkLinearClause x (ps, rhs) =
  unless (null xs) $ throwError $ unlines
    ["Nonlinear occurrence of variables in patterns."
    , "Variables: " ++ show xs
    , "Function: " ++ show x
    , "Patterns: " ++ show ps
    ]
  where xs = nonLinearVars ps

nonLinearVars :: Pats -> [Name]
nonLinearVars ps = xs \\ nub xs
  where xs = patternsVars ps

patternsVars :: Pats -> [Name]
patternsVars = concat . map (patternVars . snd)

patternVars :: Pat -> [Name]
patternVars (PVar x) = [x]
patternVars (Inacc _) = []
patternVars (PCon _ ps) = patternsVars ps

----------------------------------------------------------------------

atomizeClauses :: [Clause] -> TCM [Clause]
atomizeClauses = mapM (\(ps, rhs) -> (,rhs) <$> atomizePatterns ps)

atomizePatterns :: Pats -> TCM Pats
atomizePatterns = mapM (\(i, p) -> (i,) <$> atomizePattern p)

atomizePattern :: Pat -> TCM Pat
atomizePattern (PVar x) = case name2pname x of
  Just x' -> lookupPSigma x' >>= \case
    Just (DCon _ _ _ _) -> return $ PCon x' []
    otherwise -> return $ PVar x
  Nothing -> return $ PVar x
atomizePattern (PCon x ps) = PCon x <$> atomizePatterns ps
atomizePattern x@(Inacc _) = return x

----------------------------------------------------------------------

checkSolved :: Exp -> Exp -> TCM Exp
checkSolved a _A = do
  a <- check a _A
  checkMetas
  return a

checkExtsSolved :: Ctx -> Exp -> Exp -> TCM Exp
checkExtsSolved _As b _B = do
  b <- checkExts _As b _B
  checkMetas
  return b

checkMetas :: TCM ()
checkMetas = do
  xs <- lookupUndefMetas
  unless (null xs) (throwUnsolvedMetas xs)

----------------------------------------------------------------------

checkExt :: Name -> Exp -> Exp -> Exp -> TCM Exp
checkExt x _A = checkExts [(x, _A)]

checkExts :: Ctx -> Exp -> Exp -> TCM Exp
checkExts _As b _B = extCtxs _As (check b _B)

inferExtBind :: Exp -> Bind -> TCM (Bind, Bind)
inferExtBind _A bnd_b = do
  (x, b) <- unbind bnd_b
  (b, _B) <- extCtx x _A (infer b)
  return (Bind x b, Bind x _B)

----------------------------------------------------------------------

check :: Exp -> Exp -> TCM Exp
check a _A = do
  (a , _A') <- infer a
  conv _A _A'
  return a

infer :: Exp -> TCM (Exp, Exp)
infer (viewSpine -> (f, as)) = do
  (f, _AB) <- inferAtom f
  (as, _B) <- checkArgs as =<< whnf _AB
  return (apps f as, _B)

checkArgs :: Args -> Exp -> TCM (Args, Exp)
checkArgs as@((Expl, _):_) _AB@(Pi Impl _ _) =
  checkArgs ((Impl, Infer):as) _AB
checkArgs [] _AB@(Pi Impl _ _) =
  checkArgs [(Impl, Infer)] _AB
checkArgs ((i1, a):as) (Pi i2 _A bnd_B) | i1 == i2 = do
  a <- check a _A
  (x, _B) <- unbind bnd_B
  (as, _B) <- checkArgs as =<< whnf =<< sub1 (x, a) _B
  return ((i1, a):as, _B)
checkArgs ((i1, a):as) _B =
  throwError "Function does not have correct Pi type"
checkArgs [] _B = return ([], _B)

inferAtom :: Exp -> TCM (Exp, Exp)
inferAtom (Var x) = lookupType x >>= \case
    Just _A -> return (Var x, _A)
    Nothing -> throwNotInScope x
inferAtom Type = return (Type, Type)
inferAtom Infer = genMeta
inferAtom (Pi i _A bnd_B) = do
  _A <- check _A Type
  (x, _B) <- unbind bnd_B
  _B <- checkExt x _A _B Type
  return (Pi i _A (Bind x _B), Type)
inferAtom (Lam i _A b) = do
  _A <- check _A Type
  (b , _B) <- inferExtBind _A b
  return (Lam i _A b, Pi i _A _B)
inferAtom _ = throwError "Inferring a non-atomic term language"

----------------------------------------------------------------------
