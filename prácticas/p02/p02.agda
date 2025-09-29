
----
---- Práctica 2: Naturales e igualdad
----

open import Data.Empty
    using (⊥; ⊥-elim)
open import Data.Bool
    using (Bool; true; false)
open import Data.Nat
    using (ℕ; zero; suc)
open import Data.Product
    using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

infixl 20 _+_
infixl 30 _*_

---- Parte A ----

-- Considerar las siguientes definiciones de la suma y el producto:

_+_ : ℕ → ℕ → ℕ
zero  + b = b
suc a + b = suc (a + b)

_*_ : ℕ → ℕ → ℕ
zero  * _ = zero
suc a * b = b + a * b

-- A.1) Demostrar que la suma es asociativa.
+-assoc : {a b c : ℕ} → (a + b) + c ≡ a + (b + c)
+-assoc {zero} {zero} {c} = refl
+-assoc {zero} {suc b} {c} = refl
+-assoc {suc a} {b} {c} = cong suc (+-assoc {a})

-- A.2) Demostrar que la suma es conmutativa.
-- Sugerencia: demostrar lemas auxiliares que prueben que:
--   a + zero = a
--   a + suc b = suc (a + b)

a+zero≡a : {a : ℕ} → a + zero ≡ a
a+zero≡a {zero} = refl
a+zero≡a {suc a} = cong suc (a+zero≡a {a})

a+sb≡s[a+b] : {a b : ℕ} → a + suc b ≡ suc (a + b)
a+sb≡s[a+b] {zero} {b} = refl
a+sb≡s[a+b] {suc a} {b} = cong suc a+sb≡s[a+b]

+-comm : {a b : ℕ} → a + b ≡ b + a
+-comm {a} {zero} = a+zero≡a
+-comm {a} {suc b} =
    begin
        a + (suc b)
    ≡⟨ a+sb≡s[a+b] ⟩
        suc (a + b)
    ≡⟨ cong suc (+-comm {a}) ⟩
        (suc b) + a
    ∎

-- Versión alternativa sin razonamiento ecuacional.
-- +-comm {a} {suc b} = trans (a+sb≡s[a+b] {a} {b}) (cong suc (+-comm {a} {b}))

-- A.3) Demostrar que el producto distribuye sobre la suma (a izquierda).
*-+-distrib-l : {a b c : ℕ} → (a + b) * c ≡ a * c + b * c
*-+-distrib-l {zero} {b} {c} = refl
*-+-distrib-l {suc a} {b} {c} =
    begin
        (suc a + b) * c
    ≡⟨⟩
        (suc (a + b)) * c
    ≡⟨⟩
        c + (a + b) * c
    ≡⟨ cong (_+_ c) (*-+-distrib-l {a}) ⟩
        c + (a * c + b * c)
    ≡⟨ sym (+-assoc {c} {a * c} {b * c}) ⟩
        (c + a * c) + b * c
    ≡⟨⟩
        suc a * c + b * c
    ∎

-- A.4) Demostrar que el producto es asociativo:
*-assoc : {a b c : ℕ} → (a * b) * c ≡ a * (b * c)
*-assoc {zero} {b} {c} = refl
*-assoc {suc a} {b} {c} =
    begin
        (suc a * b) * c
    ≡⟨⟩
        (b + a * b) * c
    ≡⟨ *-+-distrib-l {b} {a * b} {c} ⟩
        b * c + a * b * c
    ≡⟨ cong (_+_ (b * c)) (*-assoc {a}) ⟩
        b * c + a * (b * c)
    ≡⟨⟩
        suc a * (b * c)
    ∎

-- A.5) Demostrar que el producto es conmutativo.
-- Sugerencia: demostrar lemas auxiliares que prueben que:
--   a * zero = zero
--   a * suc b = a + a * b

a*zero≡zero : {a : ℕ} → a * zero ≡ zero
a*zero≡zero {zero} = refl
a*zero≡zero {suc a} = a*zero≡zero {a}

a*sb≡a+a*b : {a b : ℕ} → a * suc b ≡ a + a * b
a*sb≡a+a*b {zero} {b} = refl
a*sb≡a+a*b {suc a} {b} = cong suc (
    begin
        b + (a * suc b)
    ≡⟨ cong (_+_ b) (a*sb≡a+a*b {a}) ⟩
        b + (a + a * b)
    ≡⟨ sym (+-assoc {b} {a} {(a * b)}) ⟩
        (b + a) + a * b
    ≡⟨ +-comm {b + a} {a * b} ⟩
        a * b + (b + a)
    ≡⟨ cong (_+_ (a * b)) (+-comm {b} {a}) ⟩
        a * b + (a + b)
    ≡⟨ +-comm {a * b} {a + b} ⟩
        (a + b) + a * b
    ≡⟨ +-assoc {a} {b} {(a * b)} ⟩
        a + (b + a * b)
    ∎)

*-comm : {a b : ℕ} → a * b ≡ b * a
*-comm {a} {zero} = a*zero≡zero {a}
*-comm {a} {suc b} =
    begin
        a * suc b
    ≡⟨ a*sb≡a+a*b {a} ⟩
        a + a * b
    ≡⟨ cong (_+_ a) (*-comm {a}) ⟩
        a + b * a
    ∎

-- A.6) Demostrar que el producto distribuye sobre la suma (a derecha).
-- Sugerencia: usar la conmutatividad y la distributividad a izquierda.
*-+-distrib-r : {a b c : ℕ} → a * (b + c) ≡ a * b + a * c
*-+-distrib-r {a} {b} {c} =
    begin
        a * (b + c)
    ≡⟨ *-comm {a} ⟩
        (b + c) * a
    ≡⟨ *-+-distrib-l {b} {c} {a} ⟩
        b * a + c * a
    ≡⟨ cong (_+_ (b * a)) (*-comm {c}) ⟩
        b * a + a * c
    ≡⟨ +-comm {b * a} {a * c} ⟩
        a * c + b * a
    ≡⟨ cong (_+_ (a * c)) (*-comm {b}) ⟩
        a * c + a * b
    ≡⟨ +-comm {a * c} {a * b} ⟩
        a * b + a * c
    ∎


--------------------------------------------------------------------------------

---- Parte B ----

-- Considerar la siguiente definición del predicado ≤ que dados dos números
-- naturales devuelve la proposición cuyos habitantes son demostraciones de que
-- n es menor o igual que m, y la siguiente función ≤? que dados dos
-- números naturales devuelve un booleano que indica si n es menor o igual que
-- n.

_≤_ : ℕ → ℕ → Set
n ≤ m = Σ[ k ∈ ℕ ] k + n ≡ m

_≤?_ : ℕ → ℕ → Bool
zero  ≤? m     = true
suc _ ≤? zero  = false
suc n ≤? suc m = n ≤? m

-- B.1) Demostrar que la función es correcta con respecto a su especificación.
-- Sugerencia: seguir el esquema de inducción con el que se define la función _≤?_.

≤?-correcta : {n m : ℕ} → (n ≤? m) ≡ true → n ≤ m
≤?-correcta {zero}  {m}     n≤m = m , (a+zero≡a {m})
≤?-correcta {suc n} {suc m} n≤m with ≤?-correcta {n} {m} n≤m
... | k , k+n≡m = k , trans (a+sb≡s[a+b] {k} {n}) (cong suc k+n≡m)

-- ≤?-correcta {suc n} {suc m} n≤m with ≤?-correcta {n} {m} n≤m
-- ... | k , k+n≡m = k , (begin
--             k + suc n
--         ≡⟨ a+sb≡s[a+b] {k} {n} ⟩
--             suc (k + n)
--         ≡⟨ cong suc k+n≡m ⟩
--             suc m
--     ∎)

-- B.2) Demostrar que es imposible que el cero sea el sucesor de algún natural:

zero-no-es-suc : {n : ℕ} → suc n ≡ zero → ⊥
zero-no-es-suc ()

-- B.3) Demostrar que la función es completa con respecto a su especificación.
-- Sugerencia: seguir el esquema de inducción con el que se define la función _≤?_.
-- * Para el caso en el que n = suc n' y m = zero, usar el ítem B.2 y propiedades de la suma.
-- * Para el caso en el que n = suc n' y m = suc m', recurrir a la hipótesis inductiva y propiedades de la suma.

≤?-completa : {n m : ℕ} → n ≤ m → (n ≤? m) ≡ true
≤?-completa {zero} {m} n≤m = refl
≤?-completa {suc n} {zero} (k , k+n≡m) = ⊥-elim (zero-no-es-suc {k + n} (begin
        suc (k + n)
    ≡⟨ sym (a+sb≡s[a+b] {k} {n}) ⟩
        k + suc n
    ≡⟨ k+n≡m ⟩
        zero
    ∎))
≤?-completa {suc n} {suc m} n≤m with ≤?-completa {n} {m}
... | p = {!  !}

-- k + suc n ≡ suc (k + n)
-- k + suc n ≡ zero
-- suc (k + n) ≡ zero

--------------------------------------------------------------------------------

---- Parte C ----

-- La siguiente función corresponde al principio de inducción en naturales:

indℕ : (C : ℕ → Set)
       (c0 : C zero)
       (cS : (n : ℕ) → C n → C (suc n))
       (n : ℕ)
       → C n
indℕ C c0 cS zero    = c0
indℕ C c0 cS (suc n) = cS n (indℕ C c0 cS n)

-- Definimos el predicado de "menor estricto" del siguiente modo:
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

-- C.1) Demostrar el principio de inducción completa, que permite recurrir a la hipótesis
-- inductiva sobre cualquier número estrictamente menor.
ind-completa : (C : ℕ → Set)
               (f : (n : ℕ)
                  → ((m : ℕ) → suc m < n → C m)
                  → C n)
               (n : ℕ)
               → C n
ind-completa C f n = {!!}

--------------------------------------------------------------------------------

---- Parte D ----

-- D.1) Usando pattern matching, definir el principio de inducción sobre la
-- igualdad:

ind≡ : {A : Set}
       {C : (a b : A) → a ≡ b → Set}
     → ((a : A) → C a a refl)
     → (a b : A) (p : a ≡ b) → C a b p
ind≡ = {!!}

-- D.2) Demostrar nuevamente la simetría de la igualdad, usando ind≡:

sym' : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym' = {!!}

-- D.3) Demostrar nuevamente la transitividad de la igualdad, usando ind≡:

trans' : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans' = {!!}

-- D.4) Demostrar nuevamente que la igualdad es una congruencia, usando ind≡:

cong' : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong' = {!!}
