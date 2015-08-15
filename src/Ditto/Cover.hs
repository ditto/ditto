module Ditto.Cover where
import Ditto.Syntax
import Ditto.Monad
import Control.Monad.Except
import Control.Applicative

----------------------------------------------------------------------

type CtxMap = (Tel, [Pat])
type Sub = [(Name, Pat)]

data Match = MSolve Sub | MStuck [Name] | MClash Name Name
data Cover = CMatch Sub Exp | CSplit Name | CMiss

----------------------------------------------------------------------

munion :: Match -> Match -> Match
munion (MSolve xs) (MSolve ys) = MSolve (xs ++ ys)
munion (MStuck xs) (MStuck ys) = MStuck (xs ++ ys)
munion (MClash x y) _ = MClash x y
munion _ (MClash x y) = MClash x y
munion (MStuck xs) _ = MStuck xs
munion _ (MStuck xs) = MStuck xs

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

--       Γ₁,    (x    :   A),  Γ₂  →      [Δ ⊢ σ]
split :: Tel -> Name -> Exp -> Tel -> TCM [CtxMap]
split = error "TODO"

findSplit :: Tel -> Name -> (Tel, Name, Exp, Tel)
findSplit = error "TODO"

----------------------------------------------------------------------

psubTel :: Tel -> Sub -> TCM Tel
psubTel = error "TODO"

psub :: Exp -> Sub -> TCM Exp
psub = error "TODO"

----------------------------------------------------------------------

cunion :: Cover -> Cover -> Cover
cunion x@(CMatch _ _) _ = x
cunion _ x@(CMatch _ _) = x
cunion x@(CSplit _) _ = x
cunion _ x@(CSplit _) = x
cunion _ _ = CMiss

----------------------------------------------------------------------

matchClause :: Clause -> [Pat] -> Cover
matchClause (ps, rhs) qs = case match ps qs of
  MSolve rs -> CMatch rs rhs
  MStuck xs -> CSplit (head xs)
  MClash _ _ -> CMiss

matchClauses :: [Clause] -> [Pat] -> Cover
matchClauses cs qs = foldl (\ acc c -> acc `cunion` matchClause c qs) CMiss cs

----------------------------------------------------------------------

     --  [σ = rhs]   Δ        δ   →  [Δ' ⊢ δ' = rhs']
cover :: [Clause] -> Tel -> [Pat] -> TCM [(Tel, [Pat], Exp)]
cover cs _As qs = case matchClauses cs qs of
  CMatch rs rhs -> do
    rhs' <- psub rhs rs
    return [(_As, qs, rhs')]
  CSplit xs -> error "TODO"
  CMiss -> throwError "Coverage error"

-- cover cs _As qs | allMatchesFail cs qs = 

isMatchFail :: Match -> Bool
isMatchFail (MClash _ _) = True
isMatchFail _ = False

allMatchesFail :: [Clause] -> [Pat] -> Bool
allMatchesFail cs qs
  = all (\ ps -> isMatchFail (match ps qs)) pss
  where pss = map fst cs


----------------------------------------------------------------------