module Algebraic.Field where

open import Algebraic.Group
open import Reasoning

record Field (F : Set) : Set where

    infixl 6 _*_

    field
        {{ g }} : AbelianGroup F

        _*_    : F → F → F
        e*     : F
        -- Here, we incorporate a nonzero requirement for invertibility at the type level.
        i*     : (a : F) → {_ : a /= AbelianGroup.e g} → F

        assoc* : ∀ (a b c : F) → (a * b) * c == a * (b * c)
        comm*  : ∀ (a b : F) → a * b == b * a
        id-l*  : ∀ (a : F) → e* * a == a
        inv-l* : ∀ (a : F) → {p : a /= AbelianGroup.e g} → i* a {p} * a == e*
        dist   : ∀ (a b c : F) → a * (AbelianGroup._·_ g b c) == AbelianGroup._·_ g (a * b) (a * c)

    open AbelianGroup g public
        renaming (_·_ to _+_; e to e+; i to i+;
                  assoc to assoc+; id-l to id-l+; inv-l to inv-l+; comm to comm+)

    foil : ∀ (a b c d : F) → (a + b) * (c + d) == a * c + a * d + b * c + b * d
    foil a b c d =
        (a + b) * (c + d)
       =[ dist (a + b) c d ]
        (a + b) * c + (a + b) * d
       =[ cong (λ f → f + (a + b) * d) (comm* (a + b) c) ]
        c * (a + b) + (a + b) * d
       =[ cong (λ f → c * (a + b) + f) ((comm* (a + b) d))]
        c * (a + b) + d * (a + b)
       =[ cong (λ f → f + d * (a + b)) (dist c a b) ]
        (c * a + c * b) + d * (a + b)
       =[ cong (λ f → c * a + c * b + f) (dist d a b) ]
        (c * a + c * b) + (d * a + d * b)
       =[ cong (λ f → (f + c * b) + (d * a + d * b)) (comm* c a) ]
        (a * c + c * b) + (d * a + d * b)
       =[ cong (λ f → (a * c + f) + (d * a + d * b)) (comm* c b) ]
        (a * c + b * c) + (d * a + d * b)
       =[ cong (λ f → (a * c + b * c) + (f + d * b)) (comm* d a) ]
        (a * c + b * c) + (a * d + d * b)
       =[ cong (λ f → (a * c + b * c) + (a * d + f)) (comm* d b) ]
        (a * c + b * c) + (a * d + b * d)
       =[ assoc+ (a * c) (b * c) (a * d + b * d) ]
        a * c + (b * c + (a * d + b * d))
       =[ cong (λ f → a * c + f) (sym (assoc+ (b * c) (a * d) (b * d))) ]
        a * c + ((b * c + a * d) + b * d)
       =[ cong (λ f → a * c + (f + b * d)) (comm+ (b * c) (a * d)) ]
        a * c + ((a * d + b * c) + b * d)
       =[ sym (assoc+ (a * c) (a * d + b * c) (b * d)) ]
        (a * c + (a * d + b * c)) + b * d
       =[ cong (λ f → f + b * d) (sym (assoc+ (a * c) (a * d) (b * c))) ]
    -- =((a * c + a * d) + b * c) + b * d
        a * c + a * d + b * c + b * d
       ∎