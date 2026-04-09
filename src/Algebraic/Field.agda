module Algebraic.Field where

open import Algebraic.Group
open import Reasoning

record Field (F : Set) : Set where

    infixl 6 _*_

    field
        {{ g }} : AbelianGroup F

        _*_     : F → F → F
        E       : F
        -- Here, we incorporate a nonzero requirement for invertibility at the type level.
        I       : ∀ (a : F) → {_ : a /= AbelianGroup.e g} → F

        assoc*  : ∀ (a b c : F) → (a * b) * c == a * (b * c)
        comm*   : ∀ (a b : F) → a * b == b * a
        id-l*   : ∀ (a : F) → E * a == a
        inv-l*  : ∀ (a : F) {p : a /= AbelianGroup.e g} → I a {p} * a == E

        dist    : ∀ (a b c : F) → a * (AbelianGroup._·_ g b c) == AbelianGroup._·_ g (a * b) (a * c)

    open AbelianGroup g public
        renaming (_·_ to _+_; {- e to e; i to i; -}
                  assoc to assoc+; id-l to id-l+; inv-l to inv-l+; 
                  comm to comm+)

    inv-r* : ∀ (a : F) {p : a /= e} → a * I a {p} == E
    inv-r* a =
        a * I a
       =[ comm* a (I a) ]
        I a * a
       =[ inv-l* a ]
        E
       ∎

    id-r* : ∀ (a : F) → a * E == a
    id-r* a =
        a * E
       =[ comm* a E ]
        E * a
       =[ id-l* a ]
        a
       ∎

    e-annihilates : ∀ (a : F) → e * a == e
    e-annihilates a =
        e * a
       =[ comm* e a ]
        a * e
       =[ sym (id-l+ (a * e)) ]
        e + (a * e)
       =[ cong (λ f → f + (a * e)) (sym (inv-l+ (e * a))) ]
        (i (e * a) + (e * a)) + (a * e)
       =[ cong (λ f → (i (e * a) + f) + (a * e)) (comm* e a) ]
        (i (e * a) + (a * e)) + (a * e)
       =[ assoc+  (i (e * a)) (a * e) (a * e) ]
        i (e * a) + ((a * e) + (a * e))
       =[ cong (λ f → i (e * a) + f) (sym (dist a e e)) ]
        i (e * a) + (a * (e + e))
       =[ cong (λ f → i (e * a) + f) (comm* a (e + e)) ]
        i (e * a) + ((e + e) * a)
       =[ cong (λ f → i (e * a) + (f * a)) (id-l+ e) ]
        i (e * a) + (e * a)
       =[ inv-l+ (e * a) ]
        e
       ∎

    inv-is-never-e : ∀ (a : F) {p : a /= e} → I a {p} /= e
    inv-is-never-e a {p} q =
       -- q         : I a {p} == e
       -- lemma     : ∀ (a : F) {p : a /= e} → I a {p} == e → a == e
       -- p (lemma) : ⊥
       p (a
         =[ sym (id-l* a) ]
          E * a
         =[ cong (λ f → f * a) (sym (inv-l* a)) ]
          (I a * a) * a
         =[ cong (λ f → (f * a) * a) q ]
          (e * a) * a
         =[ cong (λ f → f * a) (e-annihilates a) ]
          e * a
         =[ e-annihilates a ]
          e 
         ∎)

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