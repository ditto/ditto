module Ditto.Sub where
import Ditto.Syntax
import Ditto.Monad
import Data.List (delete)
import Control.Applicative
import Control.Monad

----------------------------------------------------------------------

fv :: Exp -> [Name]
fv (Var x) = [x]
fv Type = []
fv (Form _ is) = concatMap fv is
fv (Con _ as) = concatMap fv as
fv (Red _ as) = concatMap fv as
fv (Pi n _A _B) = fv _A ++ (n `delete` (fv _B))
fv (Lam n _A a) = fv _A ++ (n `delete` (fv a))
fv (a :@: b) = fv a ++ fv b

----------------------------------------------------------------------

sub :: (Name , Exp) -> Exp -> TCM Exp
sub (x, a) (Form y is) = Form y <$> mapM (sub (x, a)) is
sub (x, a) (Con y as) = Con y <$> mapM (sub (x, a)) as
sub (x, a) (Red y as) = Red y <$> mapM (sub (x, a)) as
sub (x, a) (Var y) | x == y = return a
sub (x, a) (Var y) = return $ Var y
sub (x, a) Type = return Type
sub (x, a) (Lam y _B b) | x == y = Lam y <$> sub (x, a) _B <*> pure b
sub (x, a) (Lam y _B b) | y `notElem` (fv a) =
  Lam y <$> sub (x, a) _B <*> sub (x, a) b
sub (x, a) (Lam y _B b) = do
  y' <- gensym
  b' <- sub (y, Var y') b
  Lam y' <$> sub (x, a) _B <*> sub (x, a) b'
sub (x, a) (Pi y _A _B) | x == y = Pi y <$> sub (x, a) _A <*> pure _B
sub (x, a) (Pi y _A _B) | y `notElem` (fv a) =
  Pi y <$> sub (x, a) _A <*> sub (x, a) _B
sub (x, a) (Pi y _A _B) = do
  y' <- gensym
  _B' <- sub (y, Var y') _B
  Pi y' <$> sub (x, a) _A <*> sub (x, a) _B'
sub (x, a) (f :@: b) = (:@:) <$> sub (x, a) f <*> sub (x, a) b

----------------------------------------------------------------------

embedPat :: Pat -> Exp
embedPat (PVar x) = Var x
embedPat (PCon x as) = Con x (map embedPat as)
embedPat (Inacc (Just a)) = a
embedPat (Inacc Nothing) = error "Inferred inaccessible cannot be embedded as a term"

----------------------------------------------------------------------

subs :: Exp -> Sub -> TCM Exp
subs = foldM (flip sub)

psubs :: Exp -> PSub -> TCM Exp
psubs a xs = subs a (map (\ (x, p) -> (x, embedPat p)) xs)

pcomp :: [Pat] -> PSub -> TCM [Pat]
pcomp = error "TODO: non-avoiding sub into pats and capture-avoid in Inacc"

----------------------------------------------------------------------