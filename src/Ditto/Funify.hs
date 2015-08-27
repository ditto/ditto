module Ditto.Funify where
import Ditto.Syntax
import Ditto.Whnf
import Ditto.Monad
import Ditto.Conv
import Ditto.Sub
import Data.List
import Control.Monad.State
import Control.Monad.Except
import Control.Applicative

----------------------------------------------------------------------

funifies :: [Name] -> [Exp] -> [Exp] -> TCM (Maybe Sub)
funifies xs as1 as2 = (Just <$> funifies' xs as1 as2)
  `catchError` const (return Nothing)

funifies' :: [Name] -> [Exp] -> [Exp] -> TCM Sub
funifies' xs [] [] = return []
funifies' xs (a1:as1) (a2:as2) = do
  s <- funify xs a1 a2
  as1' <- subs s as1
  as2' <- subs s as2
  -- TODO this may need to be substitution composition
  (s++) <$> funifies' xs as1' as2'
  where subs s = mapM (flip sub s)
funifies' _ _ _ = throwError "Unifiying equations of differing lengths"

funify :: [Name] -> Exp -> Exp -> TCM Sub
funify xs a1 a2 = do
  a1' <- whnf a1
  a2' <- whnf a2
  funify' xs a1' a2'

funify' :: [Name] -> Exp -> Exp -> TCM Sub
funify' xs (Var x) a | x `elem` xs && x `notElem` fv a = return [(x, a)]
funify' xs a (Var x) | x `elem` xs && x `notElem` fv a = return [(x, a)]
funify' xs (Con x1 as1) (Con x2 as2) | x1 == x2 = funifies' xs as1 as2
funify' xs a1 a2 = conv a1 a2 >> return []

----------------------------------------------------------------------