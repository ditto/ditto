module Ditto.Surf where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Ditto.Whnf
import Data.Maybe

----------------------------------------------------------------------

skipWrap :: PName -> Env -> Env
skipWrap x [] = []
skipWrap x (a:as) | isNamed (pname2name x) a = as
skipWrap x as = as

surfs :: Env -> TCM Prog
surfs [] = return []
surfs (Def x a _A:xs) =
  (:) <$> (SDef x <$> surfExp a <*> surfExp _A) <*> surfs xs
surfs (DForm _X _Is:(skipWrap _X -> xs)) = do
  let cs = conSigs $ filter (isConOf _X) xs
  cs <- mapM (\(y, _As, is) -> (y,) <$> surfExp (conType _As _X is)) cs
  (:) <$> (SData _X <$> surfExp (formType _Is) <*> return cs) <*> surfs xs
surfs (DCon x _As _X _Is:(skipWrap x -> xs)) = surfs xs
surfs (DRed x cs _As _B:(skipWrap x -> xs)) = do
  cs <- mapM (\(_, ps, rhs) -> (,) <$> surfPats ps <*> surfRHS rhs) cs
  (:) <$> (SDefn x <$> surfExp (pis _As _B) <*> return cs) <*> surfs xs
surfs (DMeta x ma _As _B:xs) = surfs xs

----------------------------------------------------------------------

surfExp :: Exp -> TCM Exp
surfExp Type = return Type
surfExp (Infer m) = Infer <$> return m
surfExp (Pi i _A _B) = Pi i <$> surfExp _A <*> surfExpExtBind i _A _B
surfExp (Lam i _A b) = Lam i <$> surfExp _A <*> surfExpExtBind i _A b
surfExp (App i f a) = App i <$> surfExp f <*> surfExp a
surfExp (Form x as) = Form x <$> surfExps as
surfExp (Con x as) = Con x <$> surfExps as
surfExp (Red x as) = Red x <$> surfExps as
surfExp (Meta x as) = lookupMeta x >>= \case
  Just a -> surfExp =<< whnf (apps a as)
  Nothing -> Meta x <$> surfExps as
surfExp (Var x) = return (Var x)

surfExps :: Args -> TCM Args
surfExps = mapM (\(i, a) -> (i,) <$> surfExp a)

surfExpExtBind :: Icit -> Exp -> Bind -> TCM Bind
surfExpExtBind i _A bnd_b = do
  (x, b) <- unbind bnd_b
  Bind x <$> extCtx i x _A (surfExp b)

----------------------------------------------------------------------

surfHoles :: Holes -> TCM Holes
surfHoles = mapM surfHole

surfHole :: Hole -> TCM Hole
surfHole (x, _As, _B) = (x,,) <$> surfTel _As <*> surfExp _B

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