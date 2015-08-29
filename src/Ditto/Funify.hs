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
funifies xs [] [] = return . Just $ []
funifies xs (a1:as1) (a2:as2) = funify xs a1 a2 >>= \case
  Nothing -> return Nothing
  Just s -> do
    as1' <- subs s as1
    as2' <- subs s as2
    funifies xs as1' as2' >>= \case
      Nothing -> return Nothing
      -- TODO this may need to be substitution composition
      Just s' -> return . Just $ s ++ s'
  where subs s = mapM (flip sub s)
funifies _ _ _ = throwError "Unifiying equations of differing lengths"

funify :: [Name] -> Exp -> Exp -> TCM (Maybe Sub)
funify xs a1 a2 = do
  a1' <- whnf a1
  a2' <- whnf a2
  funify' xs a1' a2'

funify' :: [Name] -> Exp -> Exp -> TCM (Maybe Sub)
funify' xs (Var x) a | x `elem` fv a = return Nothing
funify' xs a (Var x) | x `elem` fv a = return Nothing
funify' xs (Var x) a | x `elem` xs = return . Just $ [(x, a)]
funify' xs a (Var x) | x `elem` xs = return . Just $ [(x, a)]
funify' xs (Con x1 as1) (Con x2 as2) | x1 /= x2 = return Nothing
funify' xs (Con x1 as1) (Con x2 as2) = funifies xs as1 as2
funify' xs a1 a2 = conv a1 a2 >> return (Just [])

----------------------------------------------------------------------