module ch0208 where

open import ch0201

record Point : Set where
  field x : Nat
        y : Nat
-- | this means
-- module Point (p : Point) where
--   x : Nat
--   y : Nat

mkPoint : Nat → Nat → Point
mkPoint a b = record{x = a; y = b}

getX : Point → Nat
getX = Point.x

abs² : Point → Nat
abs² p = let open Point p in x * x + y * y

record Monad (M : Set → Set) : Set1 where
  field
    return : {A : Set} → A → M A
    _>>=_  : {A B : Set} → M A → (A → M B) → M B

  mapM : {A B : Set} → (A → M B) → List A → M (List B)
  mapM f [] = return []
  mapM f (x :: xs) = f x >>= λ y →
                     mapM f xs >>= λ ys →
                     return (y :: ys)

mapM' : {M : Set → Set} → Monad M →
        {A B : Set} → (A → M B) → List A → M (List B)
mapM' Mon f xs = Monad.mapM Mon f xs
