module Ditto.Match where
import Ditto.Syntax
import Ditto.Monad
import Control.Monad.Except
import Control.Applicative

----------------------------------------------------------------------

data Match = MSolve PSub | MStuck [Name] | MClash PName PName
data Cover = CMatch PSub Exp | CSplit Name | CMiss

----------------------------------------------------------------------

munion :: Match -> Match -> Match
munion (MSolve xs) (MSolve ys) = MSolve (xs ++ ys)
munion (MStuck xs) (MStuck ys) = MStuck (xs ++ ys)
munion (MClash x y) _ = MClash x y
munion _ (MClash x y) = MClash x y
munion (MStuck xs) _ = MStuck xs
munion _ (MStuck ys) = MStuck ys

----------------------------------------------------------------------

match1 :: Pat -> Pat -> Match
match1 (PVar x) p = MSolve [(x, p)]
match1 (Inacc _) _ = MSolve []
match1 (PCon x ps) (PCon y qs) | x == y = match ps qs
match1 (PCon x _) (PCon y _) = MClash x y
match1 (PCon x ps) (PVar y) = MStuck [y]
match1 (PCon x ps) (Inacc _) = MStuck []

match :: [Pat] -> [Pat] -> Match
match [] [] = MSolve []
match (p:ps) (q:qs) = match1 p q `munion` match ps qs
match _ _ = error "matching pattern clauses of different lengths"

----------------------------------------------------------------------

cunion :: Cover -> Cover -> Cover
cunion x@(CMatch _ _) _ = x
cunion x@(CSplit _) _ = x
cunion _ y = y

----------------------------------------------------------------------

matchClause :: Clause -> [Pat] -> Cover
matchClause (ps, rhs) qs = case match ps qs of
  MSolve rs -> CMatch rs rhs
  MStuck xs -> CSplit (head xs)
  MClash _ _ -> CMiss

matchClauses :: [Clause] -> [Pat] -> Cover
matchClauses cs qs = foldl (\ acc c -> acc `cunion` matchClause c qs) CMiss cs

----------------------------------------------------------------------

isMatch :: Match -> Bool
isMatch (MSolve _) = True
isMatch _ = False

unreachableClauses :: [Clause] -> [CheckedClause] -> [Clause]
unreachableClauses cs cs' =
  filter (\(ps, _) -> not (any isMatch (map (match ps) qss))) cs
  where qss = map (\(_, qs, _) -> qs) cs'

----------------------------------------------------------------------