module Algebraic.Field where

open import Algebraic.Group
open import Reasoning

record Field (F : Set) : Set where

    infixl 6 _*_

    field
        {{ g }} : AbelianGroup F

        _*_ : F → F → F
        e*  : F
        -- Here, we incorporate a nonzero requirement for invertibility at the type level.
        i*  : (a : F) → {_ : a /= AbelianGroup.e g} → F

        assoc : ∀ (a b c : F) → (a * b) * c == a * (b * c)
        comm  : ∀ (a b : F) → a * b == b * a
        id-l  : ∀ (a : F) → e* * a == a
        inv-l : ∀ (a : F) → {p : a /= AbelianGroup.e g} → i* a {p} * a == e*
        dist  : ∀ (a b c : F) → a * (AbelianGroup._·_ g b c) == AbelianGroup._·_ g (a * b) (a * c)

    open AbelianGroup g public
        renaming (_·_ to _+_; e to e+; i to i+)

