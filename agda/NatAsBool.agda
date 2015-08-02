module NatAsBool where
open import Data.Bool

ℕ : Set
ℕ = Bool

zero : ℕ
zero = true

suc : ℕ → ℕ
suc n = false

elimℕ : (P : ℕ → Set)
  (pz : P zero)
  (ps : (n : ℕ) → P n → P (suc n))
  (n : ℕ) → P n
elimℕ P pz ps true = pz
elimℕ P pz ps false = ps true pz
