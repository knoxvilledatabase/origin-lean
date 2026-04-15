/-
Extracted from RingTheory/SimpleModule/WedderburnArtin.lean
Genuine: 3 of 12 | Dissolved: 7 | Infrastructure: 2
-/
import Origin.Core

/-!
# Wedderburn–Artin Theorem

## Main results

* `IsSimpleRing.tfae`: a simple ring is semisimple iff it is Artinian,
  iff it has a minimal left ideal.

* `isSimpleRing_isArtinianRing_iff`: a ring is simple Artinian iff it is semisimple, isotypic,
  and nontrivial.

* `IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite`: a simple Artinian algebra is
  isomorphic to a (finite-dimensional) matrix algebra over a division algebra. The division
  algebra is the opposite of the endomorphism algebra of a simple (i.e., minimal) left ideal.

* `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite`: a semisimple algebra is
  isomorphic to a finite direct product of matrix algebras over division algebras. The division
  algebras are the opposites of the endomorphism algebras of the simple (i.e., minimal)
  left ideals.

* `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`,
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`:
  if the simple Artinian / semisimple algebra is finite as a module over a base ring, then the
  division algebra(s) are also finite over the same ring.
  If the base ring is an algebraically closed field, the only finite-dimensional division algebra
  over it is itself, and we obtain `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed` and
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` (in a later file).

-/

universe u

variable (R₀ : Type*) {R : Type u} [CommSemiring R₀] [Ring R] [Algebra R₀ R]

theorem IsSimpleRing.isSemisimpleRing_iff_isArtinianRing [IsSimpleRing R] :
    IsSemisimpleRing R ↔ IsArtinianRing R := tfae.out 0 1

theorem isSimpleRing_isArtinianRing_iff :
    IsSimpleRing R ∧ IsArtinianRing R ↔ IsSemisimpleRing R ∧ IsIsotypic R R ∧ Nontrivial R := by
  refine ⟨fun ⟨_, _⟩ ↦ ?_, fun ⟨_, _, _⟩ ↦ ?_⟩
  on_goal 1 => have := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr ‹_›
  all_goals simp_rw [isIsotypic_iff_isFullyInvariant_imp_bot_or_top,
      isFullyInvariant_iff_isTwoSided, isSimpleRing_iff_isTwoSided_imp] at *
  · exact ⟨this, by rwa [and_comm]⟩
  · exact ⟨⟨‹_›, ‹_›⟩, inferInstance⟩

namespace IsSimpleRing

variable (R) [IsSimpleRing R] [IsArtinianRing R]

-- INSTANCE (free from Core): (priority

theorem isIsotypic (M) [AddCommGroup M] [Module R M] : IsIsotypic R M :=
  (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).2.1.of_self M

-- DISSOLVED: exists_ringEquiv_matrix_end_mulOpposite

-- DISSOLVED: exists_ringEquiv_matrix_divisionRing

-- DISSOLVED: exists_algEquiv_matrix_end_mulOpposite

-- DISSOLVED: exists_algEquiv_matrix_divisionRing

-- DISSOLVED: exists_algEquiv_matrix_divisionRing_finite

end IsSimpleRing

namespace IsSemisimpleModule

open Module (End)

universe v

variable (R) (M : Type v) [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
  [IsSemisimpleModule R M] [Module.Finite R M]

-- DISSOLVED: exists_end_algEquiv_pi_matrix_end

-- DISSOLVED: exists_end_ringEquiv_pi_matrix_end
