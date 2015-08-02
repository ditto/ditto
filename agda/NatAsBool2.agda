module NatAsBool2 where
open import Data.Bool

ℕ : Set
ℕ = Bool

zero : ℕ
zero = true

-- modulo 2 arithmetic
-- i.e. suc of 1 is 0
suc : ℕ → ℕ
suc true = false
suc false = true

elimℕ : (P : ℕ → Set)
  (pz : P zero)
  (ps : (n : ℕ) → P n → P (suc n))
  (n : ℕ) → P n
elimℕ P pz ps true = pz
elimℕ P pz ps false = ps true pz
