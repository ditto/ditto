module Ditto.Cover where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Match
import Ditto.Sub
import Control.Monad.Except
import Control.Applicative

----------------------------------------------------------------------

type CtxMap = (Tel, [Pat])

----------------------------------------------------------------------

--       Γ₁,    (x    :   A),  Γ₂  →      [Δ ⊢ σ]
split :: Tel -> Name -> Exp -> Tel -> TCM [CtxMap]
split = error "TODO"

findSplit :: Tel -> Name -> (Tel, Name, Exp, Tel)
findSplit = error "TODO"

----------------------------------------------------------------------

     --  [σ = rhs]   Δ        δ   →  [Δ' ⊢ δ' = rhs']
cover :: [Clause] -> Tel -> [Pat] -> TCM [(Tel, [Pat], Exp)]
cover cs _As qs = case matchClauses cs qs of
  CMatch rs rhs -> do
    rhs' <- psubs rhs rs
    return [(_As, qs, rhs')]
  CSplit xs -> error "TODO"
  CMiss -> throwError "Coverage error"

----------------------------------------------------------------------