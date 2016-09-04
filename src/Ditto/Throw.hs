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
  EConv <$> surfExp a <*> surfExp b

throwAtomErr :: Exp -> TCM a
throwAtomErr a = throwErr (EAtom a)

throwUnsolvedErr :: [Prob] -> Holes -> TCM a
throwUnsolvedErr ps hs = resetCtx [] [] $ throwErr =<<
  EUnsolved <$> surfProbs ps <*> surfHoles hs

throwSplitErr :: CheckedClauses -> TCM a
throwSplitErr cs = throwErr =<<
  ESplit <$> surfClauses cs

----------------------------------------------------------------------

throwReachErr :: PName -> [Clause] -> TCM a
throwReachErr x cs = throwErr (EReach x cs)

throwGenErr :: String -> TCM a
throwGenErr = throwErr . EGen

throwScopeErr :: Name -> TCM a
throwScopeErr = throwErr . EScope

throwCaselessErr :: Name -> TCM a
throwCaselessErr = throwErr . ECaseless

----------------------------------------------------------------------

throwProbErr :: Prob -> TCM a
throwProbErr (Prob1 acts' ctx' a1 a2) =
  resetCtx acts' ctx'(throwConvErr a1 a2)
throwProbErr (ProbN p _ _ _ _) = throwProbErr p

----------------------------------------------------------------------

throwErr :: Err -> TCM a
throwErr err = do
  env <- getEnv
  prog <- surfs env
  acts <- surfActs =<< getActs
  ctx <- surfTel =<< getCtx
  throwError (defNames env, prog, acts, ctx, err)

----------------------------------------------------------------------