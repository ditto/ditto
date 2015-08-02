module NatAsBool3 where
open import Data.Bool

ℕ : Set
ℕ = Bool

zero : ℕ
zero = true

-- inconsistent
-- i.e. identify 0 and 1
suc : ℕ → ℕ
suc true = true
suc false = false

elimℕ : (P : ℕ → Set)
  (pz : P zero)
  (ps : (n : ℕ) → P n → P (suc n))
  (n : ℕ) → P n
elimℕ P pz ps true = pz
elimℕ P pz ps false = {!!}
