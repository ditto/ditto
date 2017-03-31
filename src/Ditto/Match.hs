module Ditto.Match where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Throw
import Ditto.Sub
import Ditto.Whnf
import Data.List
import Control.Monad

----------------------------------------------------------------------

data Match = MSolve PSub | MStuck [Name] | MClash
data Cover = CMatch PSub RHS | CSplit [Name] | CMiss

----------------------------------------------------------------------

munion :: Match -> Match -> Match
munion (MSolve xs) (MSolve ys) = MSolve (xs ++ ys)
munion (MStuck xs) (MStuck ys) = MStuck (xs `union` ys)
munion MClash _ = MClash
munion _ MClash = MClash
munion (MStuck xs) _ = MStuck xs
munion _ (MStuck ys) = MStuck ys

----------------------------------------------------------------------

match1 :: Pat -> Pat -> TCM Match
match1 (PVar x) p = return $ MSolve [(x, p)]
match1 (PInacc _) _ = return $ MSolve []
match1 (PCon x ps) (PCon y qs) | x == y = match ps qs
match1 (PCon x _) (PCon y _) = return MClash
match1 (PCon x ps) (PVar y) = return $ MStuck [y]
match1 (PCon x ps) (PInacc (Just a)) = matchInacc x ps a
match1 (PCon x ps) (PInacc Nothing) = throwGenErr "Undefined inaccessible in covering"

matchInacc :: PName -> Pats -> Exp -> TCM Match
matchInacc x ps a = whnf a >>= \case
  ECon y as -> match1 (PCon x ps) (PCon y (injectExps as))
  (viewSpine -> (EVar y, as)) -> return $ MStuck [y]
  _ -> throwGenErr "Ill-formed match"

match :: Pats -> Pats -> TCM Match
match [] [] = return $ MSolve []
match ((i1, p):ps) ((i2, q):qs) | i1 == i2 = munion <$> match1 p q <*> match ps qs
match ps@((Expl, _):_) ((Impl, _):qs) = match ps qs
match []               ((Impl, _):qs) = match [] qs
match ((i1, p):ps) ((i2, q):qs) | i1 /= i2 = throwGenErr "Implicit and explicit patterns mismatch"
match _ _ = throwGenErr "Matching pattern clauses of different lengths"

----------------------------------------------------------------------

cunion :: Cover -> Cover -> Cover
cunion x@(CMatch _ _) _ = x
cunion x@(CSplit _) _ = x
cunion _ y = y

----------------------------------------------------------------------

matchClause :: Clause -> Pats -> TCM Cover
matchClause (ps, rhs) qs = match ps qs >>= \case
  MSolve rs -> return $ CMatch rs rhs
  MStuck xs -> return $ CSplit xs
  MClash -> return CMiss

matchClauses :: [Clause] -> Pats -> TCM Cover
matchClauses cs qs = foldM (\ acc c -> cunion acc <$> matchClause c qs) CMiss cs

----------------------------------------------------------------------

isCovered :: Cover -> Bool
isCovered (CMatch _ _) = True
isCovered _ = False

reachable :: [Clause] -> [Clause] -> Pats -> TCM [Clause]
reachable prev [] qs = return []
reachable prev (c:cs) qs = do
  prevUnreached <- not . isCovered <$> matchClauses prev qs
  currReached <- isCovered <$> matchClause c qs
  if prevUnreached && currReached then (c:) <$> rec else rec
  where rec = reachable (snoc prev c) cs qs

reachableClauses :: [Clause] -> CheckedClauses -> TCM [Clause]
reachableClauses cs cs' = nub . concat <$> mapM (reachable [] cs) qss
  where qss = map (\(_, qs, _) -> qs) cs'

unreachableClauses :: [Clause] -> CheckedClauses -> TCM [Clause]
unreachableClauses cs cs' = (cs \\) <$> reachableClauses cs cs'

----------------------------------------------------------------------