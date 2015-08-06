module WithConstruct where
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Vec
open import Data.Bool

Bin = Bool

foo' : (A : Set) → A ≡ Bin → A → A ≡ Bin → Bin
foo' .Bin refl a q = a

foo : ℕ → ((λ x → x) ℕ) ≡ Bin → Bin
-- foo n q = foo' ℕ q n q
-- compute to normal form modulo ρ, then syntactically replace
foo n q with (λ x → x) ℕ | q
foo n q | .Bin | refl = {!!}

bar : Vec Bool (1 + 2) → Vec Bool 3 ≡ Bin → Bin
bar xs q with (λ x → x) (Vec Bool (2 + 1)) | q
bar xs q | .Bin | refl = {!!}

hm : (m n : ℕ) → Vec Bool (m + n) → (m + n) ≡ (n + m) → Bool
hm m n xs q with (m + n) | q
... | .(n + m) | refl = {!!}

