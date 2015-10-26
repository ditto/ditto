module Ditto.Throw (
    throwGenErr
  , throwConvErr
  , throwAtomErr
  , throwScopeErr
  , throwCaselessErr
  , throwMetasErr
  , throwCoverErr
  , throwReachErr
  , throwSplitErr
  ) where
import Ditto.Syntax
import Ditto.Monad
import Control.Monad.Except

----------------------------------------------------------------------

throwConvErr :: Exp -> Exp -> TCM a
throwConvErr a b = throwErr (EConv a b)

throwAtomErr :: Exp -> TCM a
throwAtomErr a = throwErr (EAtom a)

throwMetasErr :: [(MName, Tel, Exp)] -> TCM a
throwMetasErr as = throwErr (EMetas as)

throwCoverErr :: Tel -> PName -> Pats -> TCM a
throwCoverErr _As x ps = throwErr (ECover _As x ps)

throwSplitErr :: [CheckedClause] -> TCM a
throwSplitErr ps = throwErr (ESplit ps)

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

throwErr :: Err -> TCM a
throwErr err = do
  env <- getEnv
  acts <- getActs
  ctx <- getCtx
  throwError (defNames env, env, acts, ctx, err)

----------------------------------------------------------------------