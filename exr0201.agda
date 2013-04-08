module exr0201 where

open import ch0201 using (Nat; zero; suc)
open import ch0204 using (Vec; []; _::_)

-- | (a) Define a function to compute a vector containing n copies of an element x.
vec : {n : Nat}{A : Set} → A → Vec A n
vec {zero} x = []
vec {suc n} x = x :: vec {n} x

-- | (b) Define point-wise application of a vector of function to a vector of arguments.
infixl 90 _$_
_$_ : {n : Nat}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
_ $ [] = []
(f :: fs) $ (x :: xs) = (f x) :: (fs $ xs)

-- | (c) Define matrix transposition in terms of these two functions.
Matrix : Set → Nat → Nat → Set
Matrix A n m = Vec (Vec A n) m

head : {n : Nat}{A : Set} → Vec A (suc n) → A
head (x :: xs) = x
tail : {n : Nat}{A : Set} → Vec A (suc n) → Vec A n
tail (x :: xs) = xs

transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
transpose {A} {zero} xss = []
transpose {A} {suc n} {zero} xss = vec []
transpose {A} {suc n} {suc m} xss = (vec head) $ xss :: transpose (vec tail $ xss)
