module BoolAsUnit where

data Unit : Set where
  tt : Unit

Bool : Set
Bool = Unit

true : Bool
true = tt

false : Bool
false = tt

elimBool : (P : Bool → Set)
  (pt : P true)
  (pf : P false)
  (b : Bool) → P b
elimBool P pt pf tt = pt
