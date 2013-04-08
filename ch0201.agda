module ch0201 where

-- Type Bool
data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

-- Type Natural Number
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = m + n * m

_or_ : Bool → Bool → Bool
false or x = x
true  or _ = true

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else x = x

infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix  5  if_then_else_

-- List a
infixr 40 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

data _* (α : Set) : Set where
  ε : α *
  _⊲_ : α → α * → α *
