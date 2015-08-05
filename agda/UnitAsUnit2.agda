module UnitAsUnit2 where

data ⊤ : Set where
  tt : ⊤

elim⊤ : (u : ⊤) (P : ⊤ → Set) (p : P tt) → P u
elim⊤ tt P p = p

elim⊤₁ : (u : ⊤) (P : ⊤ → Set₁) (p : P tt) → P u
elim⊤₁ tt P p = p

Unit : Set
Unit = ⊤

unit : Unit
unit = tt

elimUnit : (u : Unit) (P : Unit → Set) (p : P unit) → P u
elimUnit = λ u P p → elim⊤ u P p

elimUnit₁ : (u : Unit) (P : Unit → Set₁) (p : P unit) → P u
elimUnit₁ = λ u P p → elim⊤₁ u P p

caseUnit₁ : Unit → (A : Set₁) → A → A
caseUnit₁ = λ u A a → elimUnit₁ u (λ _ → A) a

typeOf : Unit → Set
-- typeOf unit = Unit
typeOf = λ u → caseUnit₁ u Set Unit

copy : (u : typeOf unit) → typeOf u
-- copy unit = tt
-- tt on rhs represents using
copy = λ u → elimUnit u typeOf tt




