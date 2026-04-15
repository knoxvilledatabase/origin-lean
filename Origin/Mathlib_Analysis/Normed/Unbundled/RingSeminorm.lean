/-
Extracted from Analysis/Normed/Unbundled/RingSeminorm.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Seminorms and norms on rings

This file defines seminorms and norms on rings. These definitions are useful when one needs to
consider multiple (semi)norms on a given ring.

## Main declarations

For a ring `R`:
* `RingSeminorm`: A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes
  nonnegative values, is subadditive and submultiplicative and such that `f (-x) = f x` for all
  `x ∈ R`.
* `RingNorm`: A seminorm `f` is a norm if `f x = 0` if and only if `x = 0`.
* `MulRingSeminorm`: A multiplicative seminorm on a ring `R` is a ring seminorm that preserves
  multiplication.
* `MulRingNorm`: A multiplicative norm on a ring `R` is a ring norm that preserves multiplication.
  `MulRingNorm R` is essentially the same as `AbsoluteValue R ℝ`, and it is recommended to
  use the latter instead to avoid duplicating results.

## Notes

The corresponding hom classes are defined in `Mathlib/Algebra/Order/Hom/Basic.lean` to be used by
absolute values; see `Mathlib/Algebra/Order/AbsoluteValue/Basic.lean` for the bundled version.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/

open NNReal

variable {R : Type*}

structure RingSeminorm (R : Type*) [NonUnitalNonAssocRing R] extends AddGroupSeminorm R where
  /-- The property of a `RingSeminorm` that for all `x` and `y` in the ring, the norm of `x * y` is
  less than the norm of `x` times the norm of `y`. -/
  mul_le' : ∀ x y : R, toFun (x * y) ≤ toFun x * toFun y

structure RingNorm (R : Type*) [NonUnitalNonAssocRing R] extends RingSeminorm R, AddGroupNorm R

structure MulRingSeminorm (R : Type*) [NonAssocRing R] extends AddGroupSeminorm R,
  MonoidWithZeroHom R ℝ

structure MulRingNorm (R : Type*) [NonAssocRing R] extends MulRingSeminorm R, AddGroupNorm R

attribute [nolint docBlame]

  RingSeminorm.toAddGroupSeminorm RingNorm.toAddGroupNorm RingNorm.toRingSeminorm

    MulRingSeminorm.toAddGroupSeminorm MulRingSeminorm.toMonoidWithZeroHom

    MulRingNorm.toAddGroupNorm MulRingNorm.toMulRingSeminorm

namespace RingSeminorm

section NonUnitalRing

variable [NonUnitalRing R]

-- INSTANCE (free from Core): funLike

-- INSTANCE (free from Core): ringSeminormClass
