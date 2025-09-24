data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (a : A) → B a → Σ A B

ind-Σ : {A : Set} {B : A → Set} {C : Σ A B → Set}
      → ((a : A) → (b : B a) → C (a , b))
      → (p : Σ A B)
      → C p
ind-Σ f (a , b) = f a b

proj₁ : {A : Set} {B : A → Set} → Σ A B → A
proj₁ (a , b) = a

proj₂ : {A : Set} {B : A → Set} → (p : Σ A B) → B (proj₁ p)
proj₂ (a , b) = b

acWeak : {A B : Set} {C : A → B → Set}
       → ((a : A) → Σ B (λ b → C a b))
       → Σ (A → B) (λ f → (a : A) → C a (f a))
acWeak p = (λ a → proj₁ (p a)) , (λ a → proj₂ (p a))
