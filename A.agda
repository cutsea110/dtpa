module A where
  open import ch0201

  private
    internal : Nat
    internal = zero

  exported : Nat → Nat
  exported n = n + internal
