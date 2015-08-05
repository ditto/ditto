{-# OPTIONS --type-in-type #-}
module UnitAsUnit where

data ⊤ : Set where
  tt : ⊤

elim⊤ : (u : ⊤) (P : ⊤ → Set) (p : P tt) → P u
elim⊤ tt P p = p

Unit : Set
Unit = ⊤

unit : Unit
unit = tt

elimUnit : (u : Unit) (P : Unit → Set) (p : P unit) → P u
elimUnit = λ u P p → elim⊤ u P p

caseUnit : Unit → (A : Set) → A → A
caseUnit = λ u A a → elimUnit u (λ _ → A) a

typeOf : Unit → Set
-- typeOf unit = Unit
typeOf = λ u → caseUnit u Set Unit

copy : (u : typeOf unit) → typeOf u
-- copy unit = tt
copy = λ u → elimUnit u typeOf tt



