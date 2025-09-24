data Bool : Set where
    false : Bool
    true  : Bool

recBool : {C : Set} → C → C → Bool → C
recBool cTrue cFalse false = cFalse
recBool cTrue cFalse true = cTrue

not : Bool → Bool
not = recBool false true
