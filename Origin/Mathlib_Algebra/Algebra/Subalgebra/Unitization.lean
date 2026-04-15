/-
Extracted from Algebra/Algebra/Subalgebra/Unitization.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relating unital and non-unital substructures

This file relates various algebraic structures and provides maps (generally algebra homomorphisms),
from the unitization of a non-unital subobject into the full structure. The range of this map is
the unital closure of the non-unital subobject (e.g., `Algebra.adjoin`, `Subring.closure`,
`Subsemiring.closure` or `StarAlgebra.adjoin`). When the underlying scalar ring is a field, for
this map to be injective it suffices that the range omits `1`. In this setting we provide suitable
`AlgEquiv` (or `StarAlgEquiv`) onto the range.

## Main declarations

* `NonUnitalSubalgebra.unitization s : Unitization R s →ₐ[R] A`:
  where `s` is a non-unital subalgebra of a unital `R`-algebra `A`, this is the natural algebra
  homomorphism sending `(r, a)` to `r • 1 + a`. The range of this map is
  `Algebra.adjoin R (s : Set A)`.
* `NonUnitalSubalgebra.unitizationAlgEquiv s : Unitization R s ≃ₐ[R] Algebra.adjoin R (s : Set A)`
  when `R` is a field and `1 ∉ s`. This is `NonUnitalSubalgebra.unitization` upgraded to an
  `AlgEquiv` onto its range.
* `NonUnitalSubsemiring.unitization : Unitization ℕ s →ₐ[ℕ] R`: the natural `ℕ`-algebra homomorphism
  from the unitization of a non-unital subsemiring `s` into the ring containing it. The range of
  this map is `subalgebraOfSubsemiring (Subsemiring.closure s)`.
  This is just `NonUnitalSubalgebra.unitization s` but we provide a separate declaration because
  there is an instance Lean can't find on its own due to `outParam`.
* `NonUnitalSubring.unitization : Unitization ℤ s →ₐ[ℤ] R`:
  the natural `ℤ`-algebra homomorphism from the unitization of a non-unital subring `s` into the
  ring containing it. The range of this map is `subalgebraOfSubring (Subring.closure s)`.
  This is just `NonUnitalSubalgebra.unitization s` but we provide a separate declaration because
  there is an instance Lean can't find on its own due to `outParam`.
* `NonUnitalStarSubalgebra s : Unitization R s →⋆ₐ[R] A`: a version of
  `NonUnitalSubalgebra.unitization` for star algebras.
* `NonUnitalStarSubalgebra.unitizationStarAlgEquiv s :`
  `Unitization R s ≃⋆ₐ[R] StarAlgebra.adjoin R (s : Set A)`:
  a version of `NonUnitalSubalgebra.unitizationAlgEquiv` for star algebras.
-/

/-! ## Subalgebras -/

namespace Unitization

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [Semiring C] [Algebra R C]

theorem lift_range_le {f : A →ₙₐ[R] C} {S : Subalgebra R C} :
    (lift f).range ≤ S ↔ NonUnitalAlgHom.range f ≤ S.toNonUnitalSubalgebra := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

theorem lift_range (f : A →ₙₐ[R] C) :
    (lift f).range = Algebra.adjoin R (NonUnitalAlgHom.range f : Set C) :=
  eq_of_forall_ge_iff fun c ↦ by rw [lift_range_le, Algebra.adjoin_le_iff]; rfl

end Unitization

namespace NonUnitalSubalgebra

section Semiring

variable {R S A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [SetLike S A]
  [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A] (s : S)

def unitization : Unitization R s →ₐ[R] A :=
  Unitization.lift (NonUnitalSubalgebraClass.subtype s)
