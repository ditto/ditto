module UnitAsBool where
open import Data.Bool

Unit : Set
Unit = Bool

tt : Unit
tt = true

elimUnit : (P : Unit → Set)
  (p : P tt)
  (u : Unit) → P u
elimUnit P p true = p
elimUnit P p false = {!p!}
