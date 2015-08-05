module ChurchBool where

Bool : Set₁
Bool = (A : Set) → A → A → A

true : Bool
true A ct cf = ct

false : Bool
false A ct cf = cf

if : (A : Set) → Bool → A → A → A
if A b ct cf = b A ct cf

if' : Bool → Bool
if' b = b

not : Bool → Bool
-- not b = λ A ct cf → {!!}
not b A ct cf = if A b cf ct
-- not b A ct cf = b A cf ct
-- not true = false
-- not false = true

