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

sub1 :: (Name , Exp) -> Exp -> TCM Exp
sub1 (x, a) (Form y is) = Form y <$> mapM (sub1 (x, a)) is
sub1 (x, a) (Con y as) = Con y <$> mapM (sub1 (x, a)) as
sub1 (x, a) (Red y as) = Red y <$> mapM (sub1 (x, a)) as
sub1 (x, a) (Var y) | x == y = return a
sub1 (x, a) (Var y) = return $ Var y
sub1 (x, a) Type = return Type
sub1 (x, a) (Lam y _B b) | x == y = Lam y <$> sub1 (x, a) _B <*> pure b
sub1 (x, a) (Lam y _B b) | y `notElem` (fv a) =
  Lam y <$> sub1 (x, a) _B <*> sub1 (x, a) b
sub1 (x, a) (Lam y _B b) = do
  y' <- gensym
  b' <- sub1 (y, Var y') b
  Lam y' <$> sub1 (x, a) _B <*> sub1 (x, a) b'
sub1 (x, a) (Pi y _A _B) | x == y = Pi y <$> sub1 (x, a) _A <*> pure _B
sub1 (x, a) (Pi y _A _B) | y `notElem` (fv a) =
  Pi y <$> sub1 (x, a) _A <*> sub1 (x, a) _B
sub1 (x, a) (Pi y _A _B) = do
  y' <- gensym
  _B' <- sub1 (y, Var y') _B
  Pi y' <$> sub1 (x, a) _A <*> sub1 (x, a) _B'
sub1 (x, a) (f :@: b) = (:@:) <$> sub1 (x, a) f <*> sub1 (x, a) b

----------------------------------------------------------------------

embedPat :: Pat -> Exp
embedPat (PVar x) = Var x
embedPat (PCon x as) = Con x (map embedPat as)
embedPat (Inacc (Just a)) = a
embedPat (Inacc Nothing) = error "Inferred inaccessible cannot be embedded as a term"

----------------------------------------------------------------------

sub :: Exp -> Sub -> TCM Exp
sub = foldM (flip sub1)

psub :: Exp -> PSub -> TCM Exp
psub a xs = sub a (map (\ (x, p) -> (x, embedPat p)) xs)

psubPat :: Pat -> PSub -> TCM Pat
psubPat (PVar x) xs = return $ maybe (PVar x) id (lookup x xs)
psubPat (PCon x ps) xs = PCon x <$> psubPats ps xs
psubPat (Inacc Nothing) xs = return $ Inacc Nothing
psubPat (Inacc (Just a)) xs = Inacc . Just <$> psub a xs

psubPats :: [Pat] -> PSub -> TCM [Pat]
psubPats ps xs = mapM (flip psubPat xs) ps

----------------------------------------------------------------------