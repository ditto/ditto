module Ditto.Check where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Env
import Ditto.Sub
import Ditto.Whnf
import Ditto.Conv
import Ditto.Solve
import Ditto.Match
import Ditto.Cover
import Ditto.Surf
import Ditto.Throw
import Ditto.Pretty
import Data.Maybe
import Data.List
import Control.Monad.State

----------------------------------------------------------------------

runPipeline :: Verbosity -> TCM a -> (a -> b) -> Either String b
runPipeline v p f = case runTCM v p of
  Left (xs, env, acts, ctx, err) ->
    Left . render . ppCtxErr v xs env acts ctx $ err
  Right a -> Right (f a)

runPipelineV = runPipeline Verbose

runCheckProg :: Verbosity -> Prog -> Either String String
runCheckProg v ds = runPipeline v (checkProg ds) post
  where
  post (xs, env, holes) = render . ppCtxHoles v xs env $ holes

----------------------------------------------------------------------

checkProg :: Prog -> TCM ([Name], Prog, Holes)
checkProg ds = do
  mapM_ checkStmt ds
  xs <- allNames
  env <- getEnv
  prog <- surfs env
  holes <- surfHoles =<< holeMetas
  return (xs, prog, holes)

checkStmt :: MStmt -> TCM ()
checkStmt (Left d) = do
  checkSig (toSig d)
  checkBod (toBod d)
checkStmt (Right ds) = do
  mapM_ (checkSig . toSig) ds
  mapM_ (checkBod . toBod) ds

checkSig :: Sig -> TCM ()
checkSig (GDef x _A) = during (ADef x) $ do
  _A <- checkSolved _A EType
  addRed x [] _A
checkSig (GData x _A) = during (AData x) $ do
  _A <- checkSolved _A EType
  (tel, end) <- splitTel _A
  case end of
    EType -> do
      addForm x tel
    otherwise -> throwGenErr "Datatype former does not end in Type"
checkSig (GDefn x _A is) = during (ADefn x) $ do
  _A <- checkSolved _A EType
  (_As, _B) <- prefixTel _A is
  addRed x _As _B

checkBod :: Bod -> TCM ()
checkBod (BDef x a) = during (ADef x) $ do
  _A <- fromJust <$> lookupType (pname2name x)
  a  <- checkSolved a _A
  addClauses x [Clause [] [] (MapsTo a)]
checkBod (BData x cs) = during (AData x) $ do
  cs <- mapM (\ (x, _A') -> (x,) <$> during (ACon x) (checkSolved _A' EType)) cs
  mapM_ (\c -> addCon =<< buildCon x c) cs
checkBod (BDefn x cs) = during (ADefn x) $ do
  cs <- atomizeClauses cs
  checkLinearClauses x cs
  Red _As _B <- fromJust <$> lookupRed x
  cs' <- cover x cs _As
  unreached <- unreachableClauses cs cs'
  unless (null unreached) $
    throwReachErr x unreached
  addClauses x =<< mapM (\(Clause _Delta lhs rhs) -> Clause _Delta lhs <$> checkRHS _Delta lhs rhs _As _B) cs'

----------------------------------------------------------------------

checkRHS :: Tel -> Pats -> RHS -> Tel -> Exp -> TCM RHS
checkRHS _Delta lhs (MapsTo a) _As _B
  = MapsTo <$> (checkExtsSolved _Delta a =<< subClauseType _B _As lhs)
checkRHS _Delta lhs (Caseless x) _ _ = split _Delta x >>= \case
  [] -> return (Caseless x)
  otherwise -> throwCaselessErr x
checkRHS _Delta lhs (Split x) _ _ = do
  cs <- splitClause x _Delta lhs
  throwSplitErr cs

----------------------------------------------------------------------

checkLinearClauses :: PName -> SClauses -> TCM ()
checkLinearClauses x = mapM_ (checkLinearClause x)

checkLinearClause :: PName -> SClause -> TCM ()
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

atomizeClauses :: SClauses -> TCM SClauses
atomizeClauses = mapM (\(ps, rhs) -> (,rhs) <$> atomizePatterns ps)

atomizePatterns :: Pats -> TCM Pats
atomizePatterns = mapM (\(i, p) -> (i,) <$> atomizePattern p)

atomizePattern :: Pat -> TCM Pat
atomizePattern (PVar x) = case name2pname x of
  Just x' -> lookupPSigma x' >>= \case
    Just (DForm _ _ _) -> return $ PCon x' []
    otherwise -> return $ PVar x
  Nothing -> return $ PVar x
atomizePattern (PCon x ps) = PCon x <$> atomizePatterns ps
atomizePattern x@(PInacc _) = return x

----------------------------------------------------------------------

checkSolved :: Exp -> Exp -> TCM Exp
checkSolved a _A = do
  a <- check a _A
  ensureSolved
  return a

checkExtsSolved :: Tel -> Exp -> Exp -> TCM Exp
checkExtsSolved _As b _B = do
  b <- checkExts _As b _B
  ensureSolved
  return b

ensureSolved :: TCM ()
ensureSolved = do
  ps <- unsolvedProbs
  hs <- unsolvedMetas
  unless (null ps && null hs) (throwUnsolvedErr ps hs)

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
  conv _A' _A >>= \case
    Nothing -> do
      solveProbs
      return a
    Just p -> do
      a <- genGuard a _A p
      solveProbs
      return a

infer :: Exp -> TCM (Exp, Exp)
infer b@(viewSpine -> (f, as)) = do
  (f, _AB) <- inferAtom f
  (as, _B) <- checkArgs as =<< whnf _AB
  return (apps f as, _B)

checkArgs :: Args -> Exp -> TCM (Args, Exp)
checkArgs as@((Expl, _):_) _AB@(EPi Impl _ _) =
  checkArgs ((Impl, EInfer MInfer):as) _AB
checkArgs [] _AB@(EPi Impl _ _) =
  checkArgs [(Impl, EInfer MInfer)] _AB
checkArgs ((i1, a):as) (EPi i2 _A bnd_B) | i1 == i2 = do
  a <- check a _A
  (x, _B) <- unbind bnd_B
  (as, _B) <- checkArgs as =<< whnf =<< sub1 (x, a) _B
  return ((i1, a):as, _B)
checkArgs as@((i, _):_) _M@(EMeta _X _) = do
  Meta _ _As _ <- lookupMeta _X
  _AB <- genMetaPi _As i
  conv _M _AB
  checkArgs as _AB
checkArgs ((i1, a):as) _B =
  throwGenErr "Function does not have correct Pi type"
checkArgs [] _B = return ([], _B)

inferAtom :: Exp -> TCM (Exp, Exp)
inferAtom (EVar x) = lookupType x >>= \case
  Just _A -> return (EVar x, _A)
  Nothing -> throwScopeErr x
inferAtom EType = return (EType, EType)
inferAtom (EInfer m) = genMeta m
inferAtom (EPi i _A bnd_B) = do
  _A <- check _A EType
  (x, _B) <- unbind bnd_B
  _B <- checkExt i x _A _B EType
  return (EPi i _A (Bind x _B), EType)
inferAtom (ELam i _A b) = do
  _A <- check _A EType
  (b , _B) <- inferExtBind i _A b
  return (ELam i _A b, EPi i _A _B)
inferAtom x = throwAtomErr x

----------------------------------------------------------------------
