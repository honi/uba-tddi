data _×_  (A B : Set) : Set where
    _,_ : A → B → A × B

recProduct : {A B C : Set} → (A → B → C) → A × B → C
recProduct f (a , b) = f a b

indProduct : {A B : Set}
           → (C : A × B → Set)
           → ((a : A) → (b : B) → C (a , b))
           → (x : A × B)
           → C x
indProduct C f (a , b) = f a b

π₁ : {A B : Set} → A × B → A
π₁ = recProduct (\a → \b → a)

π₂ : {A B : Set} → A × B → B
π₂ = recProduct (\a → \b → b)

curry : {A B : Set}
      → (C : A × B → Set)
      → ((x : A × B) → C x)
      → (a : A)
      → (b : B)
      → C (a , b)
curry C f a b = f (a , b)

uncurry : {A B : Set}
        → (C : A × B → Set)
        → ((a : A) → (b : B) → C (a , b))
        → (x : A × B)
        → C x
uncurry = indProduct
