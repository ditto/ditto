module Ditto.Delta where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except

----------------------------------------------------------------------

deltaExpand :: Exp -> TCM Exp
deltaExpand Type = return Type
deltaExpand (Infer m) = return (Infer m)
deltaExpand (Pi i _A _B) = Pi i <$> deltaExpand _A <*> deltaExpandExtBind i _A _B
deltaExpand (Lam i _A b) = Lam i <$> deltaExpand _A <*> deltaExpandExtBind i _A b
deltaExpand (App i f a) = App i <$> deltaExpand f <*> deltaExpand a
deltaExpand (Form x as) = Form x <$> deltaExpands as
deltaExpand (Con x as) = Con x <$> deltaExpands as
deltaExpand (Red x as) = Red x <$> deltaExpands as
deltaExpand (Meta x as) = lookupMeta x >>= \case
  Just a -> deltaExpand (apps a as)
  Nothing -> Meta x <$> deltaExpands as
deltaExpand (Var x) = lookupDef x >>= \case
  Just a -> deltaExpand a
  Nothing -> return $ Var x

deltaExpands :: Args -> TCM Args
deltaExpands = mapM $ \(i, a) -> (i,) <$> deltaExpand a 

deltaExpandExtBind :: Icit -> Exp -> Bind -> TCM Bind
deltaExpandExtBind i _A bnd_b = do
  (x, b) <- unbind bnd_b
  Bind x <$> extCtx i x _A (deltaExpand b)

----------------------------------------------------------------------