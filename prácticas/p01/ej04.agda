data ⊥ : Set where

⊥-elim : {C : Set} → ⊥ → C
⊥-elim ()

teo1 : {A B : Set} → (A → ⊥) → A → B
teo1 not-a a = ⊥-elim (not-a a)
