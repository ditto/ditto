module Ditto.Surf where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Ditto.Whnf

----------------------------------------------------------------------

surfs :: Env -> TCM Prog
surfs [] = return []
surfs (Def x a _A:xs) =
  (:) <$> (SDef x <$> surfExp a <*> surfExp _A) <*> surfs xs
surfs (DForm _X _Is:(tail -> xs)) = do
  let cs = conSigs $ filter (isConOf _X) xs
  cs <- mapM (\(y, _As, is) -> (y,) <$> surfExp (conType _As _X is)) cs
  (:) <$> (SData _X <$> surfExp (formType _Is) <*> return cs) <*> surfs xs
surfs (DCon x _As _X _Is:(tail -> xs)) = surfs xs
surfs (DRed x cs _As _B:xs) = do
  cs <- mapM (\(_, ps, rhs) -> (,) <$> surfPats ps <*> surfRHS rhs) cs
  (:) <$> (SDefn x <$> surfExp (pis _As _B) <*> return cs) <*> surfs xs
surfs (DMeta x ma _As _B:xs) =
  (:) <$> (SMeta x <$> traverse surfExp ma <*> surfExp (pis _As _B)) <*> surfs xs

surfPats :: Pats -> TCM Pats
surfPats = return

surfRHS :: RHS -> TCM RHS
surfRHS = return

surfExp :: Exp -> TCM Exp
surfExp = return

----------------------------------------------------------------------