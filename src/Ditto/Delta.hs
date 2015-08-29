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
deltaExpand (Pi _A _B) = Pi <$> deltaExpand _A <*> deltaExpandExtBind _A _B
deltaExpand (Lam _A b) = Lam <$> deltaExpand _A <*> deltaExpandExtBind _A b
deltaExpand (f :@: a) = (:@:) <$> deltaExpand f <*> deltaExpand a
deltaExpand (Form x as) = Form x <$> mapM deltaExpand as
deltaExpand (Con x as) = Con x <$> mapM deltaExpand as
deltaExpand (Red x as) = Red x <$> mapM deltaExpand as
deltaExpand (Var x) = lookupDef x >>= \case
  Just a -> deltaExpand a
  Nothing -> return $ Var x

deltaExpandExtBind :: Exp -> Bind -> TCM Bind
deltaExpandExtBind _A bnd_b = do
  (x, b) <- unbind bnd_b
  Bind x <$> extCtx x _A (deltaExpand b)

----------------------------------------------------------------------