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

duringInfer :: Exp -> TCM a -> TCM a
duringInfer a = during (AInfer a)

duringCheck :: Exp -> Exp -> TCM a -> TCM a
duringCheck a _A m = flip during m =<<
  ACheck a <$> surfExp _A

duringConv :: Exp -> Exp -> TCM a -> TCM a
duringConv a b m = flip during m =<<
  AConv <$> surfExp a <*> surfExp b

duringCover :: PName -> Pats -> TCM a -> TCM a
duringCover x ps m = flip during m =<<
  ACover x <$> surfPats ps

----------------------------------------------------------------------

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
  -- TODO surface ctx if we start using the types
  ctx <- getCtx
  local (\ r -> r { acts = (ctx, x):acts r }) m

----------------------------------------------------------------------