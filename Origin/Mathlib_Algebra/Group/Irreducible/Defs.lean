/-
Extracted from Algebra/Group/Irreducible/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Irreducible elements in a monoid

This file defines irreducible elements of a monoid (`Irreducible`), as non-units that can't be
written as the product of two non-units. This generalises irreducible elements of a ring.
We also define the additive variant (`AddIrreducible`).

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Prime`
(see `irreducible_iff_prime`), however this is not true in general.
-/

assert_not_exists MonoidWithZero IsOrderedMonoid Multiset

variable {M : Type*}

structure AddIrreducible [AddMonoid M] (p : M) : Prop where
  /-- An irreducible element is not an additive unit. -/
  not_isAddUnit : ¬IsAddUnit p
  /-- If an irreducible element can be written as a sum, then one term is an additive unit. -/
  isAddUnit_or_isAddUnit ⦃a b⦄ : p = a + b → IsAddUnit a ∨ IsAddUnit b

section Monoid

variable [Monoid M] {p q a b : M}
