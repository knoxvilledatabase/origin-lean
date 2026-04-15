/-
Extracted from RingTheory/Localization/Pi.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Localizing a product of commutative rings

## Main Result

* `bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom`: the canonical map from a
    localization of a finite product of rings `R i` at a monoid `M` to the direct product of
    localizations `R i` at the projection of `M` onto each corresponding factor is bijective.

## Implementation notes

See `Mathlib/RingTheory/Localization/Defs.lean` for a design overview.

## Tags
localization, commutative ring
-/

namespace IsLocalization

variable {ι : Type*} (R S : ι → Type*)
  [Π i, CommSemiring (R i)] [Π i, CommSemiring (S i)] [Π i, Algebra (R i) (S i)]

-- INSTANCE (free from Core): (M

variable (S' : Type*) [CommSemiring S'] [Algebra (Π i, R i) S'] (M : Submonoid (Π i, R i))

theorem iff_map_piEvalRingHom [Finite ι] :
    IsLocalization M S' ↔ IsLocalization (.pi .univ fun i ↦ M.map (Pi.evalRingHom R i)) S' :=
  iff_of_le_of_exists_dvd M _ (fun m hm i _ ↦ ⟨m, hm, rfl⟩) fun n hn ↦ by
    choose m mem eq using hn
    have := Fintype.ofFinite ι
    refine ⟨∏ i, m i ⟨⟩, prod_mem fun i _ ↦ mem i _, pi_dvd_iff.mpr fun i ↦ ?_⟩
    rw [Fintype.prod_apply]
    exact (eq i ⟨⟩).symm.dvd.trans (Finset.dvd_prod_of_mem _ <| Finset.mem_univ _)

variable [∀ i, IsLocalization (M.map (Pi.evalRingHom R i)) (S i)]

lemma isUnit_piRingHom_algebraMap_comp_piEvalRingHom (y : M) :
    IsUnit ((Pi.ringHom fun i ↦ (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i)) y) :=
  Pi.isUnit_iff.mpr fun i ↦ map_units _ (⟨y.1 i, y, y.2, rfl⟩ : M.map (Pi.evalRingHom R i))

theorem bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom [IsLocalization M S'] [Finite ι] :
    Function.Bijective (lift (S := S') (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M)) :=
  have := (iff_map_piEvalRingHom R (Π i, S i) M).mpr inferInstance
  (ringEquivOfRingEquiv (M := M) (T := M) _ _ (.refl _) <|
    Submonoid.map_equiv_eq_comap_symm _ _).bijective

open Function Ideal

include M in

variable {R} in

lemma surjective_piRingHom_algebraMap_comp_piEvalRingHom
    [∀ i, Ring.KrullDimLE 0 (R i)] [∀ i, IsLocalRing (R i)] :
    Surjective (Pi.ringHom (fun i ↦ (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i))) := by
  apply Surjective.piMap (fun i ↦ ?_)
  by_cases h₀ : (0 : R i) ∈ (M.map (Pi.evalRingHom R i))
  · have := uniqueOfZeroMem h₀ (S := (S i))
    exact surjective_to_subsingleton (algebraMap (R i) (S i))
  · exact (IsLocalization.atUnits _ _ (by simpa)).surjective

variable {R} in

lemma algebraMap_pi_surjective_of_isLocalization [∀ i, Ring.KrullDimLE 0 (R i)]
    [∀ i, IsLocalRing (R i)] [IsLocalization M S']
    [Finite ι] : Surjective (algebraMap (Π i, R i) S') := by
  intro s
  set S := fun (i : ι) => Localization (M.map (Pi.evalRingHom R i))
  obtain ⟨r, hr⟩ :=
    surjective_piRingHom_algebraMap_comp_piEvalRingHom
    S M ((lift (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M)) s)
  refine ⟨r, (bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom R S _ M).injective ?_⟩
  rwa [lift_eq (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M) r]

end IsLocalization
