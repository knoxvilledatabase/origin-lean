/-
Extracted from RingTheory/Spectrum/Prime/Chevalley.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chevalley's theorem

In this file we provide the usual (algebraic) version of Chevalley's theorem.
For the proof see `Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean`.
-/

variable {R S : Type*} [CommRing R] [CommRing S]

open Function Localization MvPolynomial Polynomial TensorProduct PrimeSpectrum Topology

open scoped Pointwise

namespace PrimeSpectrum

lemma isConstructible_comap_C
    {s : Set (PrimeSpectrum (Polynomial R))} (hs : IsConstructible s) :
    IsConstructible (comap Polynomial.C '' s) := by
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  obtain ⟨T, hT, -⟩ := ChevalleyThm.chevalley_polynomialC _ Submodule.mem_top S (by simp)
  rw [hT]
  exact T.isConstructible_toSet

lemma isConstructible_comap_image
    {f : R →+* S} (hf : f.FinitePresentation)
    {s : Set (PrimeSpectrum S)} (hs : IsConstructible s) :
    IsConstructible (comap f '' s) := by
  refine hf.polynomial_induction
    (fun _ _ _ _ f ↦ ∀ s, IsConstructible s → IsConstructible (comap f '' s))
    (fun _ _ _ _ f ↦ ∀ s, IsConstructible s → IsConstructible (comap f '' s))
    (fun _ _ _ ↦ isConstructible_comap_C) ?_ ?_ f s hs
  · intro R _ S _ f hf hf' s hs
    refine hs.image_of_isClosedEmbedding (isClosedEmbedding_comap_of_surjective _ f hf) ?_
    rw [range_comap_of_surjective _ f hf]
    exact isRetrocompact_zeroLocus_compl_of_fg hf'
  · intro R _ S _ T _ f g H₁ H₂ s hs
    simp only [comap_comp, Set.image_comp]
    exact H₁ _ (H₂ _ hs)

lemma isConstructible_range_comap {f : R →+* S} (hf : f.FinitePresentation) :
    IsConstructible (Set.range <| comap f) :=
  Set.image_univ ▸ isConstructible_comap_image hf .univ
