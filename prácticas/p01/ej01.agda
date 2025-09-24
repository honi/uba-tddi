flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

compose : {A B C : Set} → (B → C) → (A → B) → A → C
compose f g a = f (g a)

-- flip: ??
-- compose: Transitividad
