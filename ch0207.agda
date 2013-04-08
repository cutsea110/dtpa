module ch0207 where

open import ch0201 using (Bool; true; false; not)
open import ch0203 using (_∘_)

import M

mapMaybe₂ : {A B : Set} → (A → B) → M.Maybe A → M.Maybe B
mapMaybe₂ f m = let open M in maybe nothing (just ∘ f) m

open M

mapManye₃ : {A B : Set} → (A → B) → Maybe A → Maybe B
mapManye₃ f m = maybe nothing (just ∘ f) m

open M hiding (maybe)
       renaming (Maybe to _option; nothing to none; just to some)

mapOption : {A B : Set} → (A → B) → A option → B option
mapOption f none     = none
mapOption f (some x) = some (f x)

mtrue : Maybe Bool
mtrue = mapOption not (just false)

module Sort (A : Set)(_<_ : A → A → Bool) where
  open import ch0201

  insert : A → List A → List A
  insert y [] = y :: []
  insert y (x :: xs) with x < y
  ... | true  = x :: insert y xs
  ... | false = y :: x :: xs

  sort : List A → List A
  sort []        = []
  sort (x :: xs) = insert x (sort xs)

open import ch0201 using (List)

sort₁ : (A : Set)(_<_ : A → A → Bool) → List A → List A
sort₁ = Sort.sort

open import ch0201 using (Nat)
open import ch0205 using (_<_)
module SortNat = Sort Nat _<_

sort₂ : List Nat → List Nat
sort₂ = SortNat.sort

open Sort Nat _<_ renaming (insert to insertNat; sort to sortNat)

module Lists (A : Set)(_<_ : A → A → Bool) where
  open import ch0201 using (List; []; _::_)
  open Sort A _<_ public
  minimum : List A → Maybe A
  minimum xs with sort xs
  ... | []      = nothing
  ... | y :: ys = just y
