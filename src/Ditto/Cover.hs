module Ditto.Cover where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Match
import Ditto.Whnf
import Ditto.Sub
import Ditto.Funify
import Data.List
import Data.Maybe
import Control.Monad.Except
import Control.Applicative

----------------------------------------------------------------------

split :: Essible -> Tel -> Name -> TCM [(Tel, PSub)]
split e _As x = splitVar e _As1 x _A _As2
  where (_As1, _A, _As2) = splitAtName _As x

splitAtName :: Tel -> Name -> (Tel, Exp, Tel)
splitAtName _As x = (_As1, _A, tail _As2) where
  (_, _, _A) = head _As2
  (_As1, _As2) = break (\ (_, y, _) -> (x == y)) _As

----------------------------------------------------------------------

--          Γ₁,    (x    :   A),  Γ₂  →      [Δ ⊢ δ']
splitVar :: Essible -> Tel -> Name -> Exp -> Tel -> TCM [(Tel, PSub)]
splitVar e _As x _B _Cs = extCtxs _As (whnf _B) >>= \case
  Form _X js -> do
    _Bs <- lookupConsFresh e _X
    catMaybes <$> mapM (\_B' -> splitCon _As x _B' js _Cs) _Bs
  otherwise -> throwGenErr "Case splitting is only allowed on datatypes"

splitCon :: Tel -> Name -> (PName, Tel, Args) -> Args -> Tel -> TCM (Maybe (Tel, PSub))
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
accPatNames ((_, PVar x):xs) = do
  y <- gensymEHint Acc x
  ((x, y):) <$> accPatNames xs
accPatNames ((_, _):xs) = accPatNames xs

----------------------------------------------------------------------

cover :: PName -> [Clause] -> Tel -> TCM [CheckedClause]
cover nm cs _As = do
  (_As', _) <- freshTel Inacc _As
  cover' nm cs _As' (pvarPats _As')

--                 [σ = rhs]   Δ       δ   →  [Δ' ⊢ δ[δ'] = rhs']
cover' :: PName -> [Clause] -> Tel -> Pats -> TCM [CheckedClause]
cover' nm cs _As qs = during (ACover nm qs) $ case matchClauses cs qs of
  CMatch rs rhs -> do
    ren <- accPatNames rs
    _As <- renTel _As ren
    qs <- psubPats qs (ren2psub ren)
    let subRHS x = psub x rs >>= flip sub (ren2sub ren) 
    case rhs of
      Caseless x -> subRHS (Var x) >>= \case
        Var x -> return [(_As, qs, Caseless x)]
        _ -> throwGenErr "Non-renaming in caseless clause"
      Split x -> subRHS (Var x) >>= \case
        Var x -> return [(_As, qs, Split x)]
        _ -> throwGenErr "Non-renaming in splitting clause"
      Prog a -> do
        a <- subRHS a
        return [(_As, qs, Prog a)]
  CSplit x -> do
    qss <- split Inacc _As x
    concat <$> mapM (\(_As' , qs') -> cover' nm cs _As' =<< psubPats qs qs') qss
  CMiss -> throwErr (ECover _As nm qs)

----------------------------------------------------------------------

splitClause :: Name -> Tel -> Pats -> TCM [CheckedClause]
splitClause x _As ps = do
  unless (x `elem` names _As) $
    extCtxs _As (throwErr (EScope x))
  qss <- split Acc _As x
  if null qss
  then return [(_As, ps, Caseless x)]
  else mapM (\(_As, qs) -> (_As,,Prog hole) <$> psubPats ps qs) qss

----------------------------------------------------------------------