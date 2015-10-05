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

runCheckProg :: Verbosity -> [Stmt] -> Either String String
runCheckProg v xs = runTCM v (checkProg xs >> lookupHoles >>= whnfHoles >>= renderHoles)

----------------------------------------------------------------------

checkProg :: [Stmt] -> TCM ()
checkProg ds = mapM_ checkStmt ds

checkStmt :: Stmt -> TCM ()
checkStmt (SDef x a _A) = during (ADef x) $ do
  _A <- checkSolved _A Type
  a  <- checkSolved a _A
  addDef x a _A
checkStmt (SData x _A cs) = during (AData x) $ do
  _A <- checkSolved _A Type
  (tel, end) <- splitTel _A
  case end of
    Type -> do
      addForm x tel
      cs <- mapM (\ (x, _A') -> (x,) <$> during (ACon x) (checkSolved _A' Type)) cs
      mapM_ (\c -> addCon =<< buildCon x c) cs
    otherwise -> throwGenErr "Datatype former does not end in Type"
checkStmt (SDefn x _A cs) = during (ADefn x) $ do
  cs <- atomizeClauses cs
  checkLinearClauses x cs
  _A <- checkSolved _A Type
  (_As, _B) <- splitTel _A
  addRedType x _As _B
  cs' <- cover x cs _As
  let unreached = unreachableClauses cs cs'
  unless (null unreached) $
    throwErr (EReach x unreached)
  addRedClauses x =<< mapM (\(_Delta, lhs, rhs) -> (_Delta, lhs,) <$> checkRHS _Delta lhs rhs _As _B) cs'

----------------------------------------------------------------------

checkRHS :: Tel -> Pats -> RHS -> Tel -> Exp -> TCM RHS
checkRHS _Delta lhs (Prog a) _As _B
  = Prog <$> (checkExtsSolved _Delta a =<< subClauseType _B _As lhs)
checkRHS _Delta lhs (Caseless x) _ _ = split _Delta x >>= \case
  [] -> return (Caseless x)
  otherwise -> throwErr (ECaseless x)
checkRHS _Delta lhs (Split x) _ _ = do
  cs <- splitClause x _Delta lhs
  throwErr (ESplit cs)

----------------------------------------------------------------------

checkLinearClauses :: PName -> [Clause] -> TCM ()
checkLinearClauses x = mapM_ (checkLinearClause x)

checkLinearClause :: PName -> Clause -> TCM ()
checkLinearClause x (ps, rhs) =
  unless (null xs) $ throwGenErr $ unlines
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
patternVars (PInacc _) = []
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
atomizePattern x@(PInacc _) = return x

----------------------------------------------------------------------

checkSolved :: Exp -> Exp -> TCM Exp
checkSolved a _A = do
  a <- check a _A
  checkMetas
  return a

checkExtsSolved :: Tel -> Exp -> Exp -> TCM Exp
checkExtsSolved _As b _B = do
  b <- checkExts _As b _B
  checkMetas
  return b

checkMetas :: TCM ()
checkMetas = do
  xs <- lookupUndefMetas
  unless (null xs) (throwErr (EMetas xs))

----------------------------------------------------------------------

checkExt :: Icit -> Name -> Exp -> Exp -> Exp -> TCM Exp
checkExt i x _A = checkExts [(i, x, _A)]

checkExts :: Tel -> Exp -> Exp -> TCM Exp
checkExts _As b _B = extCtxs _As (check b _B)

inferExtBind :: Icit -> Exp -> Bind -> TCM (Bind, Bind)
inferExtBind i _A bnd_b = do
  (x, b) <- unbind bnd_b
  (b, _B) <- extCtx i x _A (infer b)
  return (Bind x b, Bind x _B)

----------------------------------------------------------------------

check :: Exp -> Exp -> TCM Exp
check a _A = during (ACheck a _A) $ do
  (a , _A') <- infer a
  conv _A' _A
  return a

infer :: Exp -> TCM (Exp, Exp)
infer b@(viewSpine -> (f, as)) = during (AInfer b) $ do
  (f, _AB) <- inferAtom f
  (as, _B) <- checkArgs as =<< whnf _AB
  return (apps f as, _B)

checkArgs :: Args -> Exp -> TCM (Args, Exp)
checkArgs as@((Expl, _):_) _AB@(Pi Impl _ _) =
  checkArgs ((Impl, Infer MInfer):as) _AB
checkArgs [] _AB@(Pi Impl _ _) =
  checkArgs [(Impl, Infer MInfer)] _AB
checkArgs ((i1, a):as) (Pi i2 _A bnd_B) | i1 == i2 = do
  a <- check a _A
  (x, _B) <- unbind bnd_B
  (as, _B) <- checkArgs as =<< whnf =<< sub1 (x, a) _B
  return ((i1, a):as, _B)
checkArgs ((i1, a):as) _B =
  throwGenErr "Function does not have correct Pi type"
checkArgs [] _B = return ([], _B)

inferAtom :: Exp -> TCM (Exp, Exp)
inferAtom (Var x) = lookupType x >>= \case
  Just _A -> return (Var x, _A)
  Nothing -> throwErr (EScope x)
inferAtom Type = return (Type, Type)
inferAtom (Infer m) = genMeta m
inferAtom (Pi i _A bnd_B) = do
  _A <- check _A Type
  (x, _B) <- unbind bnd_B
  _B <- checkExt i x _A _B Type
  return (Pi i _A (Bind x _B), Type)
inferAtom (Lam i _A b) = do
  _A <- check _A Type
  (b , _B) <- inferExtBind i _A b
  return (Lam i _A b, Pi i _A _B)
inferAtom _ = throwGenErr "Inferring a non-atomic term language"

----------------------------------------------------------------------
