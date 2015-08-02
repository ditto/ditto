module BoolAsNat where
open import Data.Nat

Bool : Set
Bool = ℕ

true : Bool
true = zero

false : Bool
false = suc zero

elimBool : (P : Bool → Set)
  (pt : P true)
  (pf : P false)
  (b : Bool) → P b
elimBool P pt pf zero = pt
elimBool P pt pf (suc n) = {! pf!}
