/-
Extracted from Algebra/DirectSum/Internal.lean
Genuine: 4 of 9 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Internally graded rings and algebras

This module provides `DirectSum.GSemiring` and `DirectSum.GCommSemiring` instances for a collection
of subobjects `A` when a `SetLike.GradedMonoid` instance is available:

* `SetLike.gnonUnitalNonAssocSemiring`
* `SetLike.gsemiring`
* `SetLike.gcommSemiring`

With these instances in place, it provides the bundled canonical maps out of a direct sum of
subobjects into their carrier type:

* `DirectSum.coeRingHom` (a `RingHom` version of `DirectSum.coeAddMonoidHom`)
* `DirectSum.coeAlgHom` (an `AlgHom` version of `DirectSum.coeLinearMap`)

Strictly the definitions in this file are not sufficient to fully define an "internal" direct sum;
to represent this case, `(h : DirectSum.IsInternal A) [SetLike.GradedMonoid A]` is
needed. In the future there will likely be a data-carrying, constructive, typeclass version of
`DirectSum.IsInternal` for providing an explicit decomposition function.

When `iSupIndep (Set.range A)` (a weaker condition than
`DirectSum.IsInternal A`), these provide a grading of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`DirectSum.toAddMonoid (fun i ↦ AddSubmonoid.inclusion <| le_iSup A i)`.

This file also provides some extra structure on `A 0`, namely:
* `SetLike.GradeZero.subsemiring`, which leads to
  * `SetLike.GradeZero.instSemiring`
  * `SetLike.GradeZero.instCommSemiring`
* `SetLike.GradeZero.subring`, which leads to
  * `SetLike.GradeZero.instRing`
  * `SetLike.GradeZero.instCommRing`
* `SetLike.GradeZero.subalgebra`, which leads to
  * `SetLike.GradeZero.instAlgebra`

## Tags

internally graded ring
-/

open DirectSum

variable {ι : Type*} {σ S R : Type*}

theorem SetLike.algebraMap_mem_graded [Zero ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedOne A] (s : S) : algebraMap S R s ∈ A 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (A 0).smul_mem s <| SetLike.one_mem_graded _

theorem SetLike.natCast_mem_graded [Zero ι] [AddMonoidWithOne R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι → σ) [SetLike.GradedOne A] (n : ℕ) : (n : R) ∈ A 0 := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact zero_mem (A 0)
  | succ _ n_ih =>
    rw [Nat.cast_succ]
    exact add_mem n_ih (SetLike.one_mem_graded _)

theorem SetLike.intCast_mem_graded [Zero ι] [AddGroupWithOne R] [SetLike σ R]
    [AddSubgroupClass σ R] (A : ι → σ) [SetLike.GradedOne A] (z : ℤ) : (z : R) ∈ A 0 := by
  cases z
  · rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact SetLike.natCast_mem_graded _ _
  · rw [Int.cast_negSucc]
    exact neg_mem (SetLike.natCast_mem_graded _ _)

section DirectSum

variable [DecidableEq ι]

/-! #### From `AddSubmonoid`s and `AddSubgroup`s -/

namespace SetLike

-- INSTANCE (free from Core): gnonUnitalNonAssocSemiring

-- INSTANCE (free from Core): gsemiring

-- INSTANCE (free from Core): gcommSemiring

-- INSTANCE (free from Core): gring

-- INSTANCE (free from Core): gcommRing

end SetLike

namespace DirectSum

section coe

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

def coeRingHom [AddMonoid ι] [SetLike.GradedMonoid A] : (⨁ i, A i) →+* R :=
  DirectSum.toSemiring (fun i => AddSubmonoidClass.subtype (A i)) rfl fun _ _ => rfl
