module Reasoning where 

-- EQUALITY

infix 4 _==_

data _==_ {A : Set} (x : A) : A → Set where
    refl : x == x

trans : ∀ {A : Set} {x y z : A} → x == y → y == z → x == z
trans refl a = a

sym : ∀ {A : Set} {x y : A} → x == y → y == x
sym refl = refl

cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x == y → f x == f y
cong f refl = refl

data ⊥ : Set where
    
_/=_ : ∀ {A : Set} → A → A → Set
a /= b = a == b → ⊥

-- EQUATIONAL REASONING

infixr 2 _=[_]_
infix  3 _∎

-- "a =[ b ] c" is an operator for equational reasoning.
-- It can be understood as "a == c because b".
_=[_]_ : ∀ {A : Set} (x {y z} : A) → x == y → y == z → x == z
_ =[ a ] b = trans a b

-- "a ∎" is an operator for indicating the end of a proof.
-- It can be understood as "wrapping up" the c in a =[ b ] c to align with the overarching type.
_∎ : ∀ {A : Set} (x : A) → x == x
_∎ _ = refl