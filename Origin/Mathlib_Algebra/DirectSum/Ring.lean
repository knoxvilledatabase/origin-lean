/-
Extracted from Algebra/DirectSum/Ring.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The typeclasses are:

* `DirectSum.GNonUnitalNonAssocSemiring A`
* `DirectSum.GSemiring A`
* `DirectSum.GRing A`
* `DirectSum.GCommSemiring A`
* `DirectSum.GCommRing A`

Respectively, these imbue the external direct sum `⨁ i, A i` with:

* `DirectSum.nonUnitalNonAssocSemiring`, `DirectSum.nonUnitalNonAssocRing`
* `DirectSum.semiring`
* `DirectSum.ring`
* `DirectSum.commSemiring`
* `DirectSum.commRing`

the base ring `A 0` with:

* `DirectSum.GradeZero.nonUnitalNonAssocSemiring`,
  `DirectSum.GradeZero.nonUnitalNonAssocRing`
* `DirectSum.GradeZero.semiring`
* `DirectSum.GradeZero.ring`
* `DirectSum.GradeZero.commSemiring`
* `DirectSum.GradeZero.commRing`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* `DirectSum.GradeZero.smul (A 0)`, `DirectSum.GradeZero.smulWithZero (A 0)`
* `DirectSum.GradeZero.module (A 0)`
* (nothing)
* (nothing)
* (nothing)

Note that in the presence of these instances, `⨁ i, A i` itself inherits an `A 0`-action.

`DirectSum.ofZeroRingHom : A 0 →+* ⨁ i, A i` provides `DirectSum.of A 0` as a ring
homomorphism.

`DirectSum.toSemiring` extends `DirectSum.toAddMonoid` to produce a `RingHom`.

## Direct sums of subobjects

Additionally, this module provides helper functions to construct `GSemiring` and `GCommSemiring`
instances for:

* `A : ι → Submonoid S`:
  `DirectSum.GSemiring.ofAddSubmonoids`, `DirectSum.GCommSemiring.ofAddSubmonoids`.
* `A : ι → Subgroup S`:
  `DirectSum.GSemiring.ofAddSubgroups`, `DirectSum.GCommSemiring.ofAddSubgroups`.
* `A : ι → Submodule S`:
  `DirectSum.GSemiring.ofSubmodules`, `DirectSum.GCommSemiring.ofSubmodules`.

If `sSupIndep A`, these provide a gradation of `⨆ i, A i`, and the mapping `⨁ i, A i →+ ⨆ i, A i`
can be obtained as `DirectSum.toMonoid (fun i ↦ AddSubmonoid.inclusion <| le_iSup A i)`.

## Tags

graded ring, filtered ring, direct sum, additive submonoid
-/

variable {ι : Type*} [DecidableEq ι]

namespace DirectSum

open DirectSum

/-! ### Typeclasses -/

section Defs

variable (A : ι → Type*)

class GNonUnitalNonAssocSemiring [Add ι] [∀ i, AddCommMonoid (A i)] extends
  GradedMonoid.GMul A where
  /-- Multiplication from the right with any graded component's zero vanishes. -/
  mul_zero : ∀ {i j} (a : A i), mul a (0 : A j) = 0
  /-- Multiplication from the left with any graded component's zero vanishes. -/
  zero_mul : ∀ {i j} (b : A j), mul (0 : A i) b = 0
  /-- Multiplication from the right between graded components distributes with respect to
  addition. -/
  mul_add : ∀ {i j} (a : A i) (b c : A j), mul a (b + c) = mul a b + mul a c
  /-- Multiplication from the left between graded components distributes with respect to
  addition. -/
  add_mul : ∀ {i j} (a b : A i) (c : A j), mul (a + b) c = mul a c + mul b c

end Defs

section Defs

variable (A : ι → Type*)

class GSemiring [AddMonoid ι] [∀ i, AddCommMonoid (A i)] extends GNonUnitalNonAssocSemiring A,
  GradedMonoid.GMonoid A where
  /-- The canonical map from ℕ to the zeroth component of a graded semiring. -/
  natCast : ℕ → A 0
  /-- The canonical map from ℕ to a graded semiring respects zero. -/
  natCast_zero : natCast 0 = 0
  /-- The canonical map from ℕ to a graded semiring respects successors. -/
  natCast_succ : ∀ n : ℕ, natCast (n + 1) = natCast n + GradedMonoid.GOne.one

class GCommSemiring [AddCommMonoid ι] [∀ i, AddCommMonoid (A i)] extends GSemiring A,
  GradedMonoid.GCommMonoid A

class GRing [AddMonoid ι] [∀ i, AddCommGroup (A i)] extends GSemiring A where
  /-- The canonical map from ℤ to the zeroth component of a graded ring. -/
  intCast : ℤ → A 0
  /-- The canonical map from ℤ to a graded ring extends the canonical map from ℕ to the underlying
  graded semiring. -/
  intCast_ofNat : ∀ n : ℕ, intCast n = natCast n
  /-- On negative integers, the canonical map from ℤ to a graded ring is the negative extension of
  the canonical map from ℕ to the underlying graded semiring. -/
  -- Porting note: -(n + 1) -> Int.negSucc
  intCast_negSucc_ofNat : ∀ n : ℕ, intCast (Int.negSucc n) = -natCast (n + 1 : ℕ)

class GCommRing [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] extends GRing A, GCommSemiring A

end Defs

theorem of_eq_of_gradedMonoid_eq {A : ι → Type*} [∀ i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i}
    {b : A j} (h : GradedMonoid.mk i a = GradedMonoid.mk j b) :
    DirectSum.of A i a = DirectSum.of A j b :=
  DFinsupp.single_eq_of_sigma_eq h

variable (A : ι → Type*)

/-! ### Instances for `⨁ i, A i` -/

section One

variable [Zero ι] [GradedMonoid.GOne A] [∀ i, AddCommMonoid (A i)]

-- INSTANCE (free from Core): :

end One

section Mul

variable [Add ι] [∀ i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

open AddMonoidHom (flip_apply coe_comp compHom)
