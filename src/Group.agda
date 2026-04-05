module Group where

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

record AbelianGroup (A : Set) : Set where

    infixl 4 _+_

    field
        g  : Group A
        comm  : ∀ (a b : A) → Group._·_ g a b == Group._·_ g b a
    
    open Group g public

    _+_ : A → A → A
    _+_ = _·_



