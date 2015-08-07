module Ditto.Sub where
import Ditto.Syntax
import Ditto.Monad
import Data.List (delete)
import Control.Applicative

fv :: Exp -> [Name]
fv (EVar x) = [x]
fv Type = []
fv (Form _ is) = concatMap fv is
fv (Con _ as) = concatMap fv as
fv (Pi n _A _B) = fv _A ++ (n `delete` (fv _B))
fv (Lam n _A a) = fv _A ++ (n `delete` (fv a))
fv (a :@: b) = fv a ++ fv b

sub :: (Name , Exp) -> Exp -> TCM Exp
sub (x, a) (Form y is) = error "sub into form not implemented"
sub (x, a) (Con y as) = error "sub into con not implemented"
sub (x, a) (EVar y) | x == y = return a
sub (x, a) (EVar y) = return $ EVar y
sub (x, a) Type = return Type
sub (x, a) (Lam y _B b) | x == y = Lam y <$> sub (x, a) _B <*> pure b
sub (x, a) (Lam y _B b) | y `notElem` (fv a) =
  Lam y <$> sub (x, a) _B <*> sub (x, a) b
sub (x, a) (Lam y _B b) = do
  y' <- gensym
  b' <- sub (y, EVar y') b
  Lam y' <$> sub (x, a) _B <*> sub (x, a) b'
sub (x, a) (Pi y _A _B) | x == y = Pi y <$> sub (x, a) _A <*> pure _B
sub (x, a) (Pi y _A _B) | y `notElem` (fv a) =
  Pi y <$> sub (x, a) _A <*> sub (x, a) _B
sub (x, a) (Pi y _A _B) = do
  y' <- gensym
  _B' <- sub (y, EVar y') _B
  Pi y' <$> sub (x, a) _A <*> sub (x, a) _B'
sub (x, a) (f :@: b) = (:@:) <$> sub (x, a) f <*> sub (x, a) b
