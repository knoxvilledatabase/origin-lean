/-
Extracted from RingTheory/RootsOfUnity/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Roots of unity

We define roots of unity in the context of an arbitrary commutative monoid,
as a subgroup of the group of units.

## Main definitions

* `rootsOfUnity n M`, for `n : ℕ` is the subgroup of the units of a commutative monoid `M`
  consisting of elements `x` that satisfy `x ^ n = 1`.

## Main results

* `rootsOfUnity.isCyclic`: the roots of unity in an integral domain form a cyclic group.

## Implementation details

It is desirable that `rootsOfUnity` is a subgroup,
and it will mainly be applied to rings (e.g. the ring of integers in a number field) and fields.
We therefore implement it as a subgroup of the units of a commutative monoid.

We have chosen to define `rootsOfUnity n` for `n : ℕ` and add a `[NeZero n]` typeclass
assumption when we need `n` to be non-zero (which is the case for most interesting statements).
Note that `rootsOfUnity 0 M` is the top subgroup of `Mˣ` (as the condition `ζ^0 = 1` is
satisfied for all units).
-/

noncomputable section

open Polynomial

open Finset

variable {M N G R S F : Type*}

variable [CommMonoid M] [CommMonoid N] [DivisionCommMonoid G]

section rootsOfUnity

variable {k l : ℕ}

def rootsOfUnity (k : ℕ) (M : Type*) [CommMonoid M] : Subgroup Mˣ where
  carrier := {ζ | ζ ^ k = 1}
  one_mem' := one_pow _
  mul_mem' _ _ := by simp_all only [Set.mem_setOf_eq, mul_pow, one_mul]
  inv_mem' _ := by simp_all only [Set.mem_setOf_eq, inv_pow, inv_one]
