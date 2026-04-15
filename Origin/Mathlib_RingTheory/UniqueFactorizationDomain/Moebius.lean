/-
Extracted from RingTheory/UniqueFactorizationDomain/Moebius.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Moebius function on a unique factorization monoid

We define the Moebius function on a unique factorization monoid.

## Main definitions

* `UniqueFactorizationMonoid.moebius`: The Moebius function on a unique factorization monoid,
  defined to be `((-1) ^ (factors a).card)` if `a` is squarefree and `0` otherwise.

## Main statements

* `IsRelPrime.moebius_mul`: The Moebius function is a multiplicative function.
-/

namespace UniqueFactorizationMonoid

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α] {a b : α}

noncomputable def moebius (a : α) : ℤ :=
  open Classical in
  if Squarefree a then ((-1) ^ (factors a).card) else 0

theorem _root_.Nat.moebius_eq (n : ℕ) : moebius n = ArithmeticFunction.moebius n := by
  rw [moebius]
  congr
  simp [Nat.factors_eq, ArithmeticFunction.cardFactors_apply]
