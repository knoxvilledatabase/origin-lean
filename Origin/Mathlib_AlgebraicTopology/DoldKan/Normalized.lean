/-
Extracted from AlgebraicTopology/DoldKan/Normalized.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Comparison with the normalized Moore complex functor

In this file, we show that when the category `A` is abelian,
there is an isomorphism `N₁_iso_normalizedMooreComplex_comp_toKaroubi` between
the functor `N₁ : SimplicialObject A ⥤ Karoubi (ChainComplex A ℕ)`
defined in `FunctorN.lean` and the composition of
`normalizedMooreComplex A` with the inclusion
`ChainComplex A ℕ ⥤ Karoubi (ChainComplex A ℕ)`.

This isomorphism shall be used in `Equivalence.lean` in order to obtain
the Dold-Kan equivalence
`CategoryTheory.Abelian.DoldKan.equivalence : SimplicialObject A ≌ ChainComplex A ℕ`
with a functor (definitionally) equal to `normalizedMooreComplex A`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

  CategoryTheory.Subobject CategoryTheory.Idempotents DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

universe v

variable {A : Type*} [Category* A] [Abelian A] {X : SimplicialObject A}

set_option backward.isDefEq.respectTransparency false in

theorem HigherFacesVanish.inclusionOfMooreComplexMap (n : ℕ) :
    HigherFacesVanish (n + 1) ((inclusionOfMooreComplexMap X).f (n + 1)) := fun j _ => by
  dsimp [AlgebraicTopology.inclusionOfMooreComplexMap, NormalizedMooreComplex.objX]
  rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ j
    (by simp)), assoc, kernelSubobject_arrow_comp, comp_zero]

theorem factors_normalizedMooreComplex_PInfty (n : ℕ) :
    Subobject.Factors (NormalizedMooreComplex.objX X n) (PInfty.f n) := by
  rcases n with _ | n
  · apply top_factors
  · rw [PInfty_f, NormalizedMooreComplex.objX, finset_inf_factors]
    intro i _
    apply kernelSubobject_factors
    exact (HigherFacesVanish.of_P (n + 1) n) i le_add_self

set_option backward.isDefEq.respectTransparency false in
