module Ditto.Cover where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Match
import Ditto.Whnf
import Ditto.Sub
import Ditto.Funify
import Data.Maybe
import Control.Monad.Except
import Control.Applicative

----------------------------------------------------------------------

split :: Tel -> Name -> TCM [(Tel, PSub)]
split _As x = splitVar _As1 x _A _As2
  where (_As1, _A, _As2) = findSplit _As x

--       Γ₁,    (x    :   A),  Γ₂  →      [Δ ⊢ δ']
splitVar :: Tel -> Name -> Exp -> Tel -> TCM [(Tel, PSub)]
splitVar _As x _B _Cs = extCtxsTel _As (whnf _B) >>= \case
  Form _X js -> do
    _Bs <- lookupConsFresh _X
    catMaybes <$> mapM (\_B' -> splitCon _As x _B' js _Cs) _Bs
  otherwise -> throwError "Case splitting is only allowed on datatypes"

splitCon :: Tel -> Name -> (PName, Tel, Args) -> Args -> Tel -> TCM (Maybe (Tel, PSub))
splitCon _As x (y, _Bs, is) js _Cs = funifies (names _As ++ names _Bs) js is >>= \case
  Nothing -> return Nothing
  Just (injectSub -> qs) -> do
    _ABs' <- refineTel (_As ++ _Bs) qs
    as <- psubPats (pvarPats _Bs) qs
    let qs' = qs ++ [(x, PCon y as)]
    _Cs' <- psubTel _Cs qs'
    return . Just $ (_ABs' ++ _Cs', qs')

findSplit :: Tel -> Name -> (Tel, Exp, Tel)
findSplit _As x = (_As1, _A, tail _As2) where
  (_, _, _A) = head _As2
  (_As1, _As2) = break (\ (_, y, _) -> (x == y)) _As

----------------------------------------------------------------------

cover :: [Clause] -> Tel -> TCM [CheckedClause]
cover cs _As = do
  (_As', _) <- freshTel _As
  cover' cs _As' (pvarPats _As')

     --  [σ = rhs]   Δ        δ   →  [Δ' ⊢ δ[δ'] = rhs']
cover' :: [Clause] -> Tel -> Pats -> TCM [CheckedClause]
cover' cs _As qs = case matchClauses cs qs of
  CMatch rs (Caseless x) -> psub (Var x) rs >>= \case
    Var x' -> return [(fromTel _As, qs, Caseless x')]
    otherwise -> throwError "Non-renaming in caseless clause"
  CMatch rs (Prog a) -> do
    a' <- psub a rs
    return [(fromTel _As, qs, Prog a')]
  CSplit x -> do
    qss <- split _As x
    concat <$> mapM (\(_As' , qs') -> cover' cs _As' =<< psubPats qs qs') qss
  CMiss -> throwError "Coverage error"

----------------------------------------------------------------------