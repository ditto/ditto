module Ditto.Cover where
import Ditto.Syntax
import Ditto.Monad
import Control.Monad.Except

----------------------------------------------------------------------

type CtxMap = (Tel, [Pat])
type Sub = [(Name, Pat)]

data Match = MStuck [Name] | MSub Sub | MFail String

----------------------------------------------------------------------

union :: Match -> Match -> Match
union (MSub xs) (MSub ys) = MSub (xs ++ ys)
union (MStuck xs) (MStuck ys) = MStuck (xs ++ ys)
union (MFail e) _ = MFail e
union _ (MFail e) = MFail e
union (MStuck xs) _ = MStuck xs
union _ (MStuck xs) = MStuck xs

----------------------------------------------------------------------

match1 :: Pat -> Pat -> Match
match1 (PVar x) p = MSub [(x, p)]
match1 (Inacc _) _ = MSub []
match1 (PCon x ps) (PCon y qs) | x == y = match ps qs
match1 (PCon x _) (PCon y _) = MFail $ "Constructors clash: " ++ x ++ " != " ++ y
match1 (PCon x ps) (PVar y) = MStuck [y]
match1 (PCon x ps) (Inacc _) = MStuck []

match :: [Pat] -> [Pat] -> Match
match [] [] = MSub []
match (p:ps) (q:qs) = match1 p q `union` match ps qs
match _ _ = error "matching pattern clauses of different lengths"

----------------------------------------------------------------------

--       Γ₁,    (x    :   A),  Γ₂  →      [Δ ⊢ σ]
split :: Tel -> Name -> Exp -> Tel -> TCM [CtxMap]
split = undefined

findSplit :: Tel -> Name -> (Tel, Name, Exp, Tel)
findSplit = undefined

----------------------------------------------------------------------