module Algebraic.Group where

open import Reasoning

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

record Group (A : Set) : Set where

    infixl 5 _·_

    field
        _·_   : A → A → A -- binary operation
        e     : A         -- identity
        i     : A → A     -- inverse
    
        assoc : ∀ (a b c : A) → (a · b) · c == a · (b · c)
        id-l  : ∀ (a : A) → e · a == a
        inv-l : ∀ (a : A) → i a · a == e

    inv-r : ∀ (a : A) → a · i a == e
    inv-r a =
        a · i a
       =[ sym (id-l (a · i a)) ]
        e · (a · i a)
       =[ sym (assoc e a (i a)) ]
        (e · a) · i a
       =[ cong (λ f → (f · a) · i a) (sym (inv-l (i a))) ]
        ((i (i a) · i a) · a) · i a
       =[ cong (λ f → f · i a) (assoc (i (i a)) (i a) a) ]
        (i (i a) · (i a · a)) · i a
       =[ cong (λ f → (i (i a) · f) · i a) (inv-l a) ]
        (i (i a) · e) · i a
       =[ assoc (i (i a)) e (i a) ]
        i (i a) · (e · i a)
       =[ cong (λ f → i (i a) · f) (id-l (i a)) ]
        i (i a) · i a
       =[ inv-l (i a) ]
        e
       ∎

    id-r : ∀ (a : A) → a · e == a
    id-r a = 
        a · e 
       =[ cong (λ f → a · f) (sym (inv-l a)) ] 
        a · (i a · a)
       =[ sym (assoc a (i a) a) ]
        (a · i a) · a
       =[ cong (λ f → f · a) (inv-r a) ]
        e · a
       =[ id-l a ]
        a 
       ∎

    inv-of-inv : ∀ (a : A) → i (i a) == a
    inv-of-inv a =
        i (i a)
       =[ sym (id-l (i (i a))) ]
        e · i (i a)
       =[ cong (λ f → f · i (i a)) (sym (inv-r a)) ]
        (a · i a) · i (i a)
       =[ assoc a (i a) (i (i a)) ]
        a · (i a · i (i a))
       =[ cong (λ f → a · f) (inv-r (i a)) ]
        a · e
       =[ id-r a ]
        a
       ∎

    unique-id : ∀ (a b : A) → b · a == a → b == e
    unique-id a b p =
        b
       =[ sym (id-r b) ]
        b · e
       =[ cong (λ f → b · f) (sym (inv-r a)) ]
        b · (a · i a)
       =[ sym (assoc b a (i a)) ]
        (b · a) · i a
       =[ cong (λ f → f · i a) p ]
        a · i a
       =[ inv-r a ]
        e
       ∎
    
    unique-inv : ∀ (a b : A) → b · a == e → b == i a
    unique-inv a b p = 
        b
       =[ sym (id-r b) ]
        b · e
       =[ cong (λ f → b · f) (sym (inv-r a)) ]
        b · (a · i a)
       =[ sym (assoc b a (i a)) ]
        (b · a) · i a
       =[ cong (λ f → f · i a) p ]
        e · i a
       =[ id-l (i a) ]
        i a
       ∎

    -- unique-id and unique-inv are specific instances of unique-soln.
    
    unique-soln : ∀ (a b c : A) → b · a == c · a → b == c
    unique-soln a b c p = 
        b
       =[ sym (id-r b) ]
        b · e
       =[ cong (λ f → b · f) (sym (inv-r a)) ]
        b · (a · i a)
       =[ sym (assoc b a (i a)) ]
        (b · a) · i a
       =[ cong (λ f → f · i a) p ]
        (c · a) · i a
       =[ assoc c a (i a) ]
        c · (a · i a)
       =[ cong (λ f → c · f) (inv-r a) ]
        c · e
       =[ id-r c ]
        c
       ∎

    -- a^n

    rep : A → Nat → A
    rep a zero    = e
    rep a (suc n) = a · rep a n

    rep-dist-+ : ∀ (a : A) (m n : Nat) → rep a (m + n) == rep a m · rep a n
    rep-dist-+ a zero n =
        rep a (zero + n)
       =[ refl ]
        rep a n
       =[ sym (id-l (rep a n)) ]
        e · rep a n
       =[ refl ]
        rep a zero · rep a n
       ∎
    rep-dist-+ a (suc m) n =
        rep a (suc m + n)
       =[ refl ]
        rep a (suc (m + n))
       =[ refl ]
        a · rep a (m + n)
       =[ cong (λ f → a · f) (rep-dist-+ a m n) ]
        a · (rep a m · rep a n)
       =[ sym (assoc a (rep a m) (rep a n)) ]
        (a · rep a m) · rep a n
       =[ refl ]
        rep a (suc m) · rep a n
       ∎

record AbelianGroup (A : Set) : Set where

    field
        g    : Group A
        comm : ∀ (a b : A) → Group._·_ g a b == Group._·_ g b a
    
    open Group g public

    rep-dist-· : ∀ (a b : A) (n : Nat) → rep (a · b) n == rep a n · rep b n
    rep-dist-· a b zero =
        rep (a · b) zero
       =[ refl ]
        e
       =[ sym (id-l e) ]
        e · e
       =[ refl ]
        rep a zero · rep b zero
       ∎
    rep-dist-· a b (suc n) =
        rep (a · b) (suc n)
       =[ refl ]
        (a · b) · rep (a · b) n
       =[ cong (λ f → (a · b) · f) (rep-dist-· a b n) ]
        (a · b) · (rep a n · rep b n)
       =[ assoc a b (rep a n · rep b n) ]
        a · (b · (rep a n · rep b n))
       =[ cong (λ f → a · f) (sym (assoc b (rep a n) (rep b n))) ]
        a · ((b · rep a n) · rep b n)
       -- Commutativity is necessary to proceed from here. ↓
       =[ cong (λ f → a · (f · rep b n)) (comm b (rep a n))]
        a · ((rep a n · b) · rep b n)
       =[ sym (assoc a (rep a n · b) (rep b n)) ]
        (a · (rep a n · b)) · rep b n
       =[ cong (λ f → f · rep b n) (sym (assoc a (rep a n) b)) ]
        ((a · rep a n) · b) · rep b n
       =[ assoc (a · rep a n) b (rep b n) ]
        (a · rep a n) · (b · rep b n)
       =[ refl ]
        rep a (suc n) · rep b (suc n)
       ∎
        
