/-
Extracted from CategoryTheory/Sites/Coherent/RegularTopology.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Description of the covering sieves of the regular topology

This file characterises the covering sieves of the regular topology.

## Main result

* `regularTopology.mem_sieves_iff_hasEffectiveEpi`: a sieve is a covering sieve for the
  regular topology if and only if it contains an effective epi.
-/

namespace CategoryTheory.regularTopology

open Limits

variable {C : Type*} [Category* C] [Preregular C] {X : C}

theorem mem_sieves_of_hasEffectiveEpi (S : Sieve X) :
    (∃ (Y : C) (π : Y ⟶ X), EffectiveEpi π ∧ S.arrows π) → (S ∈ (regularTopology C) X) := by
  rintro ⟨Y, π, h⟩
  have h_le : Sieve.generate (Presieve.ofArrows (fun () ↦ Y) (fun _ ↦ π)) ≤ S := by
    rw [Sieve.generate_le_iff (Presieve.ofArrows _ _) S]
    apply Presieve.le_of_factorsThru_sieve (Presieve.ofArrows _ _) S _
    intro W g f
    refine ⟨W, 𝟙 W, ?_⟩
    cases f
    exact ⟨π, ⟨h.2, Category.id_comp π⟩⟩
  apply Coverage.saturate_of_superset (regularCoverage C) h_le
  exact Coverage.Saturate.of X _ ⟨Y, π, rfl, h.1⟩

-- INSTANCE (free from Core): {Y

theorem mem_sieves_iff_hasEffectiveEpi (S : Sieve X) :
    (S ∈ (regularTopology C) X) ↔
    ∃ (Y : C) (π : Y ⟶ X), EffectiveEpi π ∧ (S.arrows π) := by
  constructor
  · intro h
    induction h with
    | of Y T hS =>
      rcases hS with ⟨Y', π, h'⟩
      refine ⟨Y', π, h'.2, ?_⟩
      rcases h' with ⟨rfl, _⟩
      exact ⟨Y', 𝟙 Y', π, Presieve.ofArrows.mk (), (by simp)⟩
    | top Y => exact ⟨Y, (𝟙 Y), inferInstance, by simp only [Sieve.top_apply]⟩
    | transitive Y R S _ _ a b =>
      rcases a with ⟨Y₁, π, ⟨h₁, h₂⟩⟩
      choose Y' π' _ H using b h₂
      exact ⟨Y', π' ≫ π, inferInstance, (by simpa using H)⟩
  · exact regularTopology.mem_sieves_of_hasEffectiveEpi S

end CategoryTheory.regularTopology
