/-
Extracted from Algebra/Ring/Action/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `MulSemiringAction M R`.

An example of a `MulSemiringAction` is the action of the Galois group `Gal(L/K)` on
the big field `L`. Note that `Algebra` does not in general satisfy the axioms
of `MulSemiringAction`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `MulSemiringAction`.

## Note

The corresponding typeclass of subrings invariant under such an action, `IsInvariantSubring`, is
defined in `Mathlib/Algebra/Ring/Action/Invariant.lean`.

## Tags

group action

-/

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul

universe u v

class MulSemiringAction (M : Type u) (R : Type v) [Monoid M] [Semiring R] extends
  DistribMulAction M R where
  /-- Multiplying `1` by a scalar gives `1` -/
  smul_one : ∀ g : M, (g • (1 : R) : R) = 1
  /-- Scalar multiplication distributes across multiplication -/
  smul_mul : ∀ (g : M) (x y : R), g • (x * y) = g • x * g • y

section Semiring

variable (M N : Type*) [Monoid M] [Monoid N]

variable (R : Type v) [Semiring R]

-- INSTANCE (free from Core): (priority
