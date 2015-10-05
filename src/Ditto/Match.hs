module Ditto.Match where
import Ditto.Syntax
import Ditto.Monad
import Data.List
import Control.Monad.Except
import Control.Applicative

----------------------------------------------------------------------

data Match = MSolve PSub | MStuck [Name] | MClash
data Cover = CMatch PSub RHS | CSplit Name | CMiss

----------------------------------------------------------------------

munion :: Match -> Match -> Match
munion (MSolve xs) (MSolve ys) = MSolve (xs ++ ys)
munion (MStuck xs) (MStuck ys) = MStuck (xs ++ ys)
munion MClash _ = MClash
munion _ MClash = MClash
munion (MStuck xs) _ = MStuck xs
munion _ (MStuck ys) = MStuck ys

----------------------------------------------------------------------

match1 :: Pat -> Pat -> Match
match1 (PVar x) p = MSolve [(x, p)]
match1 (PInacc _) _ = MSolve []
match1 (PCon x ps) (PCon y qs) | x == y = match ps qs
match1 (PCon x _) (PCon y _) = MClash
match1 (PCon x ps) (PVar y) = MStuck [y]
match1 (PCon x ps) (PInacc _) = MStuck []

match :: Pats -> Pats -> Match
match [] [] = MSolve []
match ((i1, p):ps) ((i2, q):qs) | i1 == i2 = match1 p q `munion` match ps qs
match ps@((Expl, _):_) ((Impl, _):qs) = match ps qs
match []               ((Impl, _):qs) = match [] qs
match ((i1, p):ps) ((i2, q):qs) | i1 /= i2 = error "Implicit and explicit patterns mismatch"
match _ _ = error "matching pattern clauses of different lengths"

----------------------------------------------------------------------

cunion :: Cover -> Cover -> Cover
cunion x@(CMatch _ _) _ = x
cunion x@(CSplit _) _ = x
cunion _ y = y

----------------------------------------------------------------------

matchClause :: Clause -> Pats -> Cover
matchClause (ps, rhs) qs = case match ps qs of
  MSolve rs -> CMatch rs rhs
  MStuck xs -> CSplit (head xs)
  MClash -> CMiss

matchClauses :: [Clause] -> Pats -> Cover
matchClauses cs qs = foldl (\ acc c -> acc `cunion` matchClause c qs) CMiss cs

----------------------------------------------------------------------

isCovered :: Cover -> Bool
isCovered (CMatch _ _) = True
isCovered _ = False

reachable :: [Clause] -> [Clause] -> Pats -> [Clause]
reachable prev [] qs = []
reachable prev (c:cs) qs = if prevUnreached && currReached then c:rec else rec
  where
  rec = reachable (snoc prev c) cs qs
  prevUnreached = not . isCovered . matchClauses prev $ qs
  currReached = isCovered (matchClause c qs)

reachableClauses :: [Clause] -> [CheckedClause] -> [Clause]
reachableClauses cs cs' = nub $ concatMap (reachable [] cs) qss
  where qss = map (\(_, qs, _) -> qs) cs'

unreachableClauses :: [Clause] -> [CheckedClause] -> [Clause]
unreachableClauses cs cs' = cs \\ reachableClauses cs cs'

----------------------------------------------------------------------