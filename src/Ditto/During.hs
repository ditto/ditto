module Ditto.During
  ( duringInfer
  , duringCheck
  , duringConv
  , duringCover
  , duringDef
  , duringData
  , duringCon
  , duringDefn
  ) where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Surf
import Control.Monad.Reader

----------------------------------------------------------------------

duringCheck :: Exp -> Exp -> TCM a -> TCM a
duringCheck a _A = during (ACheck a _A)

duringConv :: Exp -> Exp -> TCM a -> TCM a
duringConv a1 a2 = during (AConv a1 a2)

duringCover :: PName -> Pats -> TCM a -> TCM a
duringCover x ps = during (ACover x ps)

----------------------------------------------------------------------

duringInfer :: Exp -> TCM a -> TCM a
duringInfer = during . AInfer

duringDef :: Name -> TCM a -> TCM a
duringDef = during . ADef

duringData :: PName -> TCM a -> TCM a
duringData = during . AData

duringCon :: PName -> TCM a -> TCM a
duringCon = during . ACon

duringDefn :: PName -> TCM a -> TCM a
duringDefn = during . ADefn

----------------------------------------------------------------------

during :: Act -> TCM a -> TCM a
during x m = do
  ctx <- getCtx
  local (\ r -> r { acts = (ctx, x):acts r }) m

----------------------------------------------------------------------