/-
Extracted from Algebra/Star/NonUnitalSubsemiring.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Non-unital Star Subsemirings

In this file we define `NonUnitalStarSubsemiring`s and the usual operations on them.

## Implementation

This file is heavily inspired by `Mathlib/Algebra/Star/NonUnitalSubalgebra.lean`.

-/

universe v w w'

variable {A : Type v} {B : Type w} {C : Type w'}

structure SubStarSemigroup (M : Type v) [Mul M] [Star M] : Type v
    extends Subsemigroup M where
  /-- The `carrier` of a `StarSubset` is closed under the `star` operation. -/
  star_mem' : ∀ {a : M} (_ha : a ∈ carrier), star a ∈ carrier

add_decl_doc SubStarSemigroup.toSubsemigroup

structure NonUnitalStarSubsemiring (R : Type v) [NonUnitalNonAssocSemiring R] [Star R] : Type v
    extends NonUnitalSubsemiring R where
  /-- The `carrier` of a `NonUnitalStarSubsemiring` is closed under the `star` operation. -/
  star_mem' : ∀ {a : R} (_ha : a ∈ carrier), star a ∈ carrier

add_decl_doc NonUnitalStarSubsemiring.toNonUnitalSubsemiring

section NonUnitalStarSubsemiring

namespace NonUnitalStarSubsemiring

-- INSTANCE (free from Core): instSetLike

initialize_simps_projections NonUnitalStarSubsemiring (carrier → coe, as_prefix coe)

variable {R : Type v} [NonUnitalNonAssocSemiring R] [StarRing R]
