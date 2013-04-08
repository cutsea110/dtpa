module exr0202 where

open import ch0201 using (Nat; zero; suc)
open import ch0203 using (_∘_)
open import ch0204
open import ch0205

-- | (a)
lem-!-tab : ∀ {A n} (f : Fin n → A)(i : Fin n) →
            (tabulate f ! i) == f i
lem-!-tab f fzero = refl
lem-!-tab f (fsuc k) = lem-!-tab (f ∘ fsuc) k

-- | (b)
-- ref. http://hpaste.org/53345
cong : ∀ {A B : Set} {x y : A} (f : A → B) → x == y → f x == f y
cong f refl = refl

lem-tab-! : ∀ {A n} (xs : Vec A n) → tabulate (_!_ xs) == xs
lem-tab-! [] = refl
lem-tab-! (x :: xs) = cong (_::_ x) (aux x xs)
  where aux : {A : Set}{n : Nat}(x : A)(xs : Vec A n) → tabulate (_!_ (x :: xs) ∘ fsuc) == xs
        aux x [] = refl
        aux x (x' :: xs) = cong (_::_ x') (aux x' xs)
