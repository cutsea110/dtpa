module exr0203 where

open import ch0201
open import ch0204
open import ch0206

-- | (a)
⊆-refl : {A : Set}{xs : List A} → xs ⊆ xs
⊆-refl {A} {[]} = stop
⊆-refl {A} {x :: xs} = keep ⊆-refl

⊆-trans : {A : Set}{xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans stop stop = stop
⊆-trans stop (drop q) = drop q
⊆-trans (drop p) (drop q) = drop (⊆-trans (drop p) q)
⊆-trans (drop p) (keep q) = drop (⊆-trans p q)
⊆-trans (keep p) (drop q) = drop (⊆-trans (keep p) q)
⊆-trans (keep p) (keep q) = keep (⊆-trans p q)

-- | (b)
infixr 30 _::_
data SubList {A : Set} : List A → Set where
  [] : SubList []
  _::_ : ∀ x {xs} → SubList xs → SubList (x :: xs)
  skip : ∀ {x xs} → SubList xs → SubList (x :: xs)
