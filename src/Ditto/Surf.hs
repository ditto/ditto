module Ditto.Surf where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Ditto.Expand
import Data.Maybe

----------------------------------------------------------------------

surfs :: Env -> TCM Prog
surfs env = map Left <$> (surfs' env [])

surfs' :: Env -> [PName] -> TCM [Stmt]
surfs' [] xs = return []
surfs' (Def x a _A:env) xs = if isDeltaName x xs
  then surfs' env xs
  else (:) <$> (SDef x <$> defBod <*> surfExp _A) <*> surfs' env xs
  where defBod = maybe (return hole) surfExp a
surfs' (DForm _X cs _Is:env) (((_X:conNames cs)++) -> xs) = do
  cs <- mapM (\(y, _As, is) -> (y,) <$> surfExp (conType _As _X is)) cs
  (:) <$> (SData _X <$> surfExp (formType _Is) <*> return cs) <*> surfs' env xs
surfs' (DRed x cs _As _B:env) ((x:) -> xs) = do
  cs <- mapM (\(_, ps, rhs) -> (,) <$> surfPats ps <*> surfRHS rhs) cs
  (:) <$> (SDefn x <$> surfExp (pis _As _B) <*> return cs) <*> surfs' env xs
surfs' (DMeta x ma acts _As _B:env) xs = surfs' env xs
surfs' (DGuard x a _A:env) xs = surfs' env xs

isDeltaName :: Name -> [PName] -> Bool
isDeltaName x xs = maybe False (flip elem xs) (name2pname x)

----------------------------------------------------------------------

surfExp = expand metaForm
surfExps = expands metaForm
surfExpBind = expandBind metaForm

----------------------------------------------------------------------

surfHoles :: Holes -> TCM Holes
surfHoles = mapM surfHole

surfHole :: Hole -> TCM Hole
surfHole (x, acts, ctx, _A) = (x,,,) <$> surfActs acts <*> surfTel ctx <*> surfExp _A

----------------------------------------------------------------------

surfActs :: Acts -> TCM Acts
surfActs = mapM (\(_As, a) -> (,) <$> surfTel _As <*> surfAct a)

surfAct :: Act -> TCM Act
surfAct (ACheck a _A) = ACheck a <$> surfExp _A
surfAct (AConv a1 a2) = AConv <$> surfExp a1 <*> surfExp a2
surfAct (ACover x ps) = ACover x <$> surfPats ps
surfAct x@(ADef _) = return x
surfAct x@(AData _) = return x
surfAct x@(ACon _) = return x
surfAct x@(ADefn _) = return x

----------------------------------------------------------------------

surfProbs :: [Prob] -> TCM [Prob]
surfProbs = mapM surfProb

surfProb :: Prob -> TCM Prob
surfProb (Prob1 acts ctx a1 a2) = Prob1 <$> surfActs acts <*> surfTel ctx <*> surfExp a1 <*> surfExp a2
surfProb (ProbN p acts ctx as1 as2) =
  ProbN <$> surfProb p <*> surfActs acts <*> surfTel ctx <*> surfExps as1 <*> surfExps as2

----------------------------------------------------------------------

surfTel :: Tel -> TCM Tel
surfTel = mapM (\(i, x, _A) -> (i,x,) <$> surfExp _A)

----------------------------------------------------------------------

surfClauses :: [CheckedClause] -> TCM [CheckedClause]
surfClauses = mapM surfClause

surfClause :: CheckedClause -> TCM CheckedClause
surfClause (_As, ps, rhs) = (,,)
  <$> surfTel _As <*> surfPats ps <*> surfRHS rhs

surfPats :: Pats -> TCM Pats
surfPats = mapM (\(i, a) -> (i,) <$> surfPat a)

surfPat :: Pat -> TCM Pat
surfPat (PVar x) = PVar <$> return x
surfPat (PInacc ma) = PInacc <$> traverse surfExp ma
surfPat (PCon x ps) = PCon x <$> surfPats ps

surfRHS :: RHS -> TCM RHS
surfRHS (MapsTo a) = MapsTo <$> surfExp a
surfRHS (Caseless x) = Caseless <$> return x
surfRHS (Split x) = Split <$> return x

----------------------------------------------------------------------