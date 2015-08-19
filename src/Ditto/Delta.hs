{-# LANGUAGE LambdaCase #-}
module Ditto.Delta where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub
import Data.Maybe
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except

----------------------------------------------------------------------

deltaExpand :: Exp -> TCM Exp
deltaExpand Type = return Type
deltaExpand (Pi x _A _B) = Pi x <$> deltaExpand _A <*> deltaExpand _B
deltaExpand (Lam x _A b) = Lam x <$> deltaExpand _A <*> deltaExpand b
deltaExpand (f :@: a) = (:@:) <$> deltaExpand f <*> deltaExpand a
deltaExpand (Form x as) = Form x <$> mapM deltaExpand as
deltaExpand (Con x as) = Con x <$> mapM deltaExpand as
deltaExpand (Red x as) = Red x <$> mapM deltaExpand as
deltaExpand (Var x) = do
  lookupDef x >>= \case
    Just a -> deltaExpand a
    Nothing -> return $ Var x

----------------------------------------------------------------------