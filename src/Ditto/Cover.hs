module Ditto.Cover where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Match
import Ditto.Whnf
import Ditto.Sub
import Ditto.Funify
import Ditto.Throw
import Data.List
import Data.Maybe
import Control.Monad.Except

----------------------------------------------------------------------

split :: Tel -> Name -> TCM [(Tel, PSub)]
split _As x = splitVar _As1 x _A _As2
  where (_As1, _A, _As2) = splitAtName _As x

splitAtName :: Tel -> Name -> (Tel, Exp, Tel)
splitAtName _As x = (_As1, _A, tail _As2) where
  (_, _, _A) = head _As2
  (_As1, _As2) = break (\ (_, y, _) -> (x == y)) _As

----------------------------------------------------------------------

--          Γ₁,    (x    :   A),  Γ₂  →      [Δ ⊢ δ']
splitVar :: Tel -> Name -> Exp -> Tel -> TCM [(Tel, PSub)]
splitVar _As x _B _Cs = whnf _B >>= \case
  Form _X js -> do
    _Bs <- lookupConsFresh _X
    catMaybes <$> mapM (\_B' -> splitCon _As x _B' js _Cs) _Bs
  otherwise -> throwGenErr "Case splitting is only allowed on datatypes"

splitCon :: Tel -> Name -> ConSig -> Args -> Tel -> TCM (Maybe (Tel, PSub))
splitCon _As x (y, _Bs, is) js _Cs = funifies (names _As ++ names _Bs) js is >>= \case
  Nothing -> return Nothing
  Just (injectSub -> qs) -> do
    _ABs' <- refineTel (_As ++ _Bs) qs
    as <- psubPats (pvarPats _Bs) qs
    let qs' = snoc qs (x, PCon y as)
    _Cs' <- psubTel _Cs qs'
    return . Just $ (_ABs' ++ _Cs', qs')

----------------------------------------------------------------------

refineTel :: Tel -> PSub -> TCM Tel
refineTel [] xs = return []
refineTel ((i, x, _A):_As) xs = case lookup x xs of
  Nothing -> ((i, x, _A):) <$> refineTel _As xs
  Just a -> let (_Bs, _Cs) = partitionByPat a _As in do
    _Cs <- psubTel1 (x, a) _Cs
    refineTel (_Bs ++ _Cs) xs

partitionByPat :: Pat -> Tel -> (Tel, Tel)
partitionByPat (fv . embedPat -> xs) = partition (\(_,x,_) -> elem x xs)

----------------------------------------------------------------------

accPatNames :: PSub -> TCM Ren
accPatNames [] = return []
accPatNames ((y, accPatName -> Just x):xs) = do
  y <- gensymHint y
  ((x, y):) <$> accPatNames xs
accPatNames ((_, _):xs) = accPatNames xs

accPatName :: Pat -> Maybe Name
accPatName (PVar x) = Just x
accPatName (PInacc (Just (Var x))) = Just x
accPatName _ = Nothing

accPSub :: PSub -> Tel -> Pats -> TCM (Tel, Pats, Exp -> TCM Exp)
accPSub rs _As qs = do
  ren <- accPatNames rs
  _As <- renTel _As ren
  qs <- psubPats qs (ren2psub ren)
  let subRHS x = psub x rs >>= flip sub (ren2sub ren)
  return (_As, qs, subRHS)

----------------------------------------------------------------------

cover :: PName -> [Clause] -> Tel -> TCM CheckedClauses
cover nm cs _As = do
  (_As', _) <- freshTel Inacc _As
  cover' nm cs _As' (pvarPats _As')

--                 [σ = rhs]   Δ       δ   →  [Δ' ⊢ δ[δ'] = rhs']
cover' :: PName -> [Clause] -> Tel -> Pats -> TCM CheckedClauses
cover' nm cs _As qs = during (ACover nm qs) $ matchClauses cs qs >>= \case
  CMatch rs rhs -> do
    (_As, qs, subRHS) <- accPSub rs _As qs
    case rhs of
      Caseless x -> subRHS (Var x) >>= \case
        Var x -> return [(_As, qs, Caseless x)]
        _ -> throwGenErr "Non-renaming in caseless clause"
      Split x -> subRHS (Var x) >>= \case
        Var x -> return [(_As, qs, Split x)]
        _ -> throwGenErr "Non-renaming in splitting clause"
      MapsTo a -> do
        a <- subRHS a
        return [(_As, qs, MapsTo a)]
  CSplit x -> do
    rss <- split _As x
    concat <$> mapM (\(_As' , rs') -> cover' nm cs _As' =<< psubPats qs rs') rss
  CMiss -> throwCoverErr _As nm qs

----------------------------------------------------------------------

splitClauseGoal :: Pats -> Tel -> Pats -> TCM CheckedClause
splitClauseGoal ps _As qs = match ps qs >>= \case
  MSolve rs -> do
    (_As, qs, _) <- accPSub rs _As qs
    return (_As, qs, MapsTo hole)
  _ -> throwGenErr "Split clause did not match original clause"

splitClause :: Name -> Tel -> Pats -> TCM CheckedClauses
splitClause x _As ps = do
  unless (x `elem` names _As) $
    extCtxs _As (throwScopeErr x)
  rss <- split _As x
  if null rss
  then return [(_As, ps, Caseless x)]
  else mapM (\(_As, rs) -> splitClauseGoal ps _As =<< psubPats ps rs) rss

----------------------------------------------------------------------