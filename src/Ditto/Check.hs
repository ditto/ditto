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
checkProg = mapM_ checkStmt

checkStmt :: Stmt -> TCM ()
checkStmt (SDef x a _A) = do
  _A <- check _A Type
  a  <- check a _A
  addDef x a _A
checkStmt (SData x _A cs) = do
  _A <- check _A Type
  (tel, end) <- splitTel _A
  case end of
    Type -> do
      addForm x tel
      cs <- mapM (\ (x, _A') -> (x,) <$> check _A' Type) cs
      mapM_ (\c -> addCon =<< buildCon x c) cs
    otherwise -> throwError "Datatype former does not end in Type"
checkStmt (SDefn x _A cs) = do
  cs <- atomizeClauses cs
  checkLinearClauses x cs
  _A <- check _A Type
  (_As, _B) <- splitTel _A
  addRedType x _As _B
  cs' <- cover cs _As
  let unreached = unreachableClauses cs cs'
  unless (null unreached) $ do
    throwError $ "Unreachable user clauses:\n"
      ++ (unlines (map show unreached))
      ++ "\nCovered by:\n"
      ++ (unlines (map show cs'))
  addRedClauses x =<< mapM (\(_Delta, lhs, rhs) -> (_Delta, lhs,) <$> checkRHS _Delta lhs rhs _As _B) cs'

----------------------------------------------------------------------

checkRHS :: Tel -> [Pat] -> RHS -> Tel -> Exp -> TCM RHS
checkRHS _Delta lhs (Prog a) _As _B
  = Prog <$> (checkExts _Delta a =<< subClauseType _B _As lhs)
checkRHS _Delta lhs (Caseless x) _As _B = split _Delta x >>= \case
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

inferExtBind :: Exp -> Bind -> TCM (Bind, Bind)
inferExtBind _A bnd_b = do
  (x, b) <- unbind bnd_b
  (b, _B) <- extCtx x _A (infer b)
  return (Bind x b, Bind x _B)

checkExt :: Name -> Exp -> Exp -> Exp -> TCM Exp
checkExt x _A = checkExts [(x, _A)]

checkExts :: Tel -> Exp -> Exp -> TCM Exp
checkExts _As b _B = extCtxs _As (check b _B)

----------------------------------------------------------------------

check :: Exp -> Exp -> TCM Exp
check a _A = do
  (a , _A') <- infer a
  conv _A _A'
  return a

infer :: Exp -> TCM (Exp, Exp)
infer (Var x) = lookupType x >>= \case
    Just _A -> return (Var x, _A)
    Nothing -> throwNotInScope x
infer Type = return (Type, Type)
infer Infer = genMeta
infer (Pi _A bnd_B) = do
  _A <- check _A Type
  (x, _B) <- unbind bnd_B
  _B <- checkExt x _A _B Type
  return (Pi _A (Bind x _B), Type)
infer (Lam _A b) = do
  _A <- check _A Type
  (b , _B) <- inferExtBind _A b
  return (Lam _A b, Pi _A _B)
infer (f :@: a) = do
  (f, _F) <- infer f
  whnf _F >>= \case
    Pi _A bnd_B -> do
      a <- check a _A
      (x, _B) <- unbind bnd_B
      (f :@: a,) <$> sub1 (x, a) _B
    otherwise -> throwError "Function does not have Pi type"
infer _ = throwError "Inferring a term not in the surface language"

----------------------------------------------------------------------
