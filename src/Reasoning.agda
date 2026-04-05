module Reasoning where 

infix 4 _==_

data _==_ {A : Set} (x : A) : A → Set where
    refl : x == x

trans : ∀ {A : Set} {x y z : A} → x == y → y == z → x == z
trans refl a = a

sym : ∀ {A : Set} {x y : A} → x == y → y == x
sym refl = refl

cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x == y → f x == f y
cong f refl = refl

infixr 2 _=[_]_
infix  3 _∎

_=[_]_ : ∀ {A : Set} (x {y z} : A) → x == y → y == z → x == z
_ =[ a ] b = trans a b

_∎ : ∀ {A : Set} (x : A) → x == x
_∎ _ = refl