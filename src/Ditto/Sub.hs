module Ditto.Sub where
import Ditto.Syntax
import Data.List

fv :: Exp -> [Name]
fv (EVar x) = [x]
fv Type = []
fv (Pi n _A _B) = fv _A ++ (n `delete` (fv _B))
fv (Lam n _A a) = fv _A ++ (n `delete` (fv a))
fv (a :@: b) = fv a ++ fv b


sub :: (Name , Exp) -> Exp -> Exp
sub = error "Subsitution not implemented"
