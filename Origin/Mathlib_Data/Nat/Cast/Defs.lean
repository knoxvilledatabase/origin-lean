/-
Extracted from Data/Nat/Cast/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cast of natural numbers

This file defines the *canonical* homomorphism from the natural numbers into an
`AddMonoid` with a one.  In additive monoids with one, there exists a unique
such homomorphism and we store it in the `natCast : ℕ → R` field.

Preferentially, the homomorphism is written as the coercion `Nat.cast`.

## Main declarations

* `NatCast`: Type class for `Nat.cast`.
* `AddMonoidWithOne`: Type class for which `Nat.cast` is a canonical monoid homomorphism from `ℕ`.
* `Nat.cast`: Canonical homomorphism `ℕ → R`.
-/

variable {R : Type*}

protected def Nat.unaryCast [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1
