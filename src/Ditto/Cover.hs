{-# LANGUAGE LambdaCase #-}
module Ditto.Cover where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Match
import Ditto.Whnf
import Ditto.Sub
import Control.Monad.Except
import Control.Applicative

----------------------------------------------------------------------

split :: Tel -> Name -> TCM [(Tel, PSub)]
split _As x = splitVar _As1 x _A _As2
  where (_As1, _A, _As2) = findSplit _As x

--       Γ₁,    (x    :   A),  Γ₂  →      [Δ ⊢ δ']
splitVar :: Tel -> Name -> Exp -> Tel -> TCM [(Tel, PSub)]
splitVar _As x _B _Cs = whnf _B >>= \case
  Form _X [] -> do
    _Bs <- lookupCons _X
    mapM (\_B -> splitCon _As x _B _Cs) _Bs
  Form _X is -> error "Splitting on indexed datatype not yet implemented"
  otherwise -> throwError "Case splitting is only allowed on datatypes"

splitCon :: Tel -> Name -> (PName, Tel, [Exp]) -> Tel -> TCM (Tel, PSub)
splitCon _As x (y, _Bs, _) _Cs = do
  _Bs' <- freshFor (names (_As ++ _Cs)) =<< freshenShadows _Bs
  let qs = [(x, PCon y (pvarNames _Bs'))]
  _Cs' <- psubTel _Cs qs
  return (_As ++ _Bs' ++ _Cs', qs)

findSplit :: Tel -> Name -> (Tel, Exp, Tel)
findSplit _As x = (_As1, snd (head _As2), tail _As2)
  where (_As1, _As2) = break ((x ==) . fst) _As

----------------------------------------------------------------------

     --  [σ = rhs]   Δ        δ   →  [Δ' ⊢ δ[δ'] = rhs']
cover :: [Clause] -> Tel -> [Pat] -> TCM [CheckedClause]
cover cs _As qs = case matchClauses cs qs of
  CMatch rs rhs -> do
    rhs' <- psub rhs rs
    return [(_As, qs, rhs')]
  CSplit x -> do
    qss <- split _As x
    concat <$> mapM (\(_As' , qs') -> cover cs _As' =<< psubPats qs qs') qss
  CMiss -> throwError "Coverage error"

----------------------------------------------------------------------