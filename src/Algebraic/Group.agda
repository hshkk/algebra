module Algebraic.Group where

open import Reasoning

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

record AbelianGroup (A : Set) : Set where

    infixl 4 _+_

    field
        g  : Group A
        comm  : ∀ (a b : A) → Group._·_ g a b == Group._·_ g b a
    
    open Group g public

    _+_ : A → A → A
    _+_ = _·_
