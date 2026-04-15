/-
Extracted from RingTheory/GradedAlgebra/Homogeneous/Subsemiring.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Homogeneous subsemirings of a graded semiring

This file defines homogeneous subsemirings of a graded semiring, as well as operations on them.

## Main definitions

* `HomogeneousSubsemiring 𝒜`: The type of subsemirings which satisfy `SetLike.IsHomogeneous`.
-/

open DirectSum Set SetLike

variable {ι σ A : Type*} [AddMonoid ι] [Semiring A]

variable [SetLike σ A] [AddSubmonoidClass σ A]

variable (𝒜 : ι → σ) [DecidableEq ι] [GradedRing 𝒜]

variable (R : Subsemiring A)

section HomogeneousDef

variable {R} in

theorem DirectSum.SetLike.IsHomogeneous.mem_iff (hR : IsHomogeneous 𝒜 R) {a} :
    a ∈ R ↔ ∀ i, (decompose 𝒜 a i : A) ∈ R :=
  AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hR

structure HomogeneousSubsemiring extends Subsemiring A where
  is_homogeneous' : IsHomogeneous 𝒜 toSubsemiring

variable {𝒜}

namespace HomogeneousSubsemiring

theorem toSubsemiring_injective :
    (toSubsemiring : HomogeneousSubsemiring 𝒜 → Subsemiring A).Injective :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]

-- INSTANCE (free from Core): setLike

-- INSTANCE (free from Core): :

theorem isHomogeneous (R : HomogeneousSubsemiring 𝒜) :
    IsHomogeneous 𝒜 R := R.is_homogeneous'

-- INSTANCE (free from Core): subsemiringClass
