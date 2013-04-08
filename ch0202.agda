module ch0202 where

open import ch0201

identity : (A : Set) → A → A
identity A x = x

zero' : Nat
zero' = identity Nat zero

apply : (A : Set)(B : A → Set) →
        ((x : A) → B x) → (a : A) → B a
apply A B f a = f a

identity₂ : (A : Set) → A → A
identity₂ = λ A x → x

identity₃ : (A : Set) → A → A
identity₃ = λ (A : Set)(x : A) → x

identity₄ : (A : Set) → A → A
identity₄ = λ (A : Set) x → x
