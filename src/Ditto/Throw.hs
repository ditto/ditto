module Ditto.Throw
  ( throwGenErr
  , throwConvErr
  , throwAtomErr
  , throwScopeErr
  , throwCaselessErr
  , throwUnsolvedErr
  , throwReachErr
  , throwSplitErr
  , throwProbErr
  ) where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Surf
import Control.Monad.Except

----------------------------------------------------------------------

throwConvErr :: Exp -> Exp -> TCM a
throwConvErr a b = throwErr =<<
  RConv <$> surfExp a <*> surfExp b

throwAtomErr :: Exp -> TCM a
throwAtomErr a = throwErr (RAtom a)

throwUnsolvedErr :: [Prob] -> Holes -> TCM a
throwUnsolvedErr ps hs = resetCtx [] [] $ throwErr =<<
  RUnsolved <$> surfProbs ps <*> surfHoles hs

throwSplitErr :: Clauses -> TCM a
throwSplitErr cs = throwErr =<<
  RSplit <$> surfClauses cs

----------------------------------------------------------------------

throwReachErr :: PName -> SClauses -> TCM a
throwReachErr x cs = throwErr (RReach x cs)

throwGenErr :: String -> TCM a
throwGenErr = throwErr . RGen

throwScopeErr :: Name -> TCM a
throwScopeErr = throwErr . RScope

throwCaselessErr :: Name -> TCM a
throwCaselessErr = throwErr . RCaseless

----------------------------------------------------------------------

throwProbErr :: Prob -> TCM a
throwProbErr (Prob1 acts' ctx' a1 a2) =
  resetCtx acts' ctx'(throwConvErr a1 a2)
throwProbErr (ProbN p _ _ _ _) = throwProbErr p

----------------------------------------------------------------------

throwErr :: Err -> TCM a
throwErr err = do
  xs <- defNames
  env <- getEnv
  prog <- surfs env
  acts <- surfActs =<< getActs
  ctx <- surfTel =<< getCtx
  throwError (xs, prog, acts, ctx, err)

----------------------------------------------------------------------