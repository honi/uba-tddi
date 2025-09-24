data ⊤ : Set where
    tt : ⊤

indUnit : {C : ⊤ -> Set} → C tt -> (x : ⊤) → C x
indUnit x tt = x
