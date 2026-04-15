/-
Extracted from CategoryTheory/Sites/JointlySurjective.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The jointly surjective precoverage

In the category of types, the jointly surjective precoverage has the jointly surjective
families as coverings. We show that this precoverage is stable under the standard constructions.

## Notes

See `Mathlib/CategoryTheory/Sites/Types.lean` for the Grothendieck topology of jointly surjective
covers.
-/

universe u

namespace CategoryTheory

open Limits

namespace Types

def jointlySurjectivePrecoverage : Precoverage (Type u) where
  coverings X R := ∀ x : X, ∃ (Y : Type u) (g : Y ⟶ X), R g ∧ x ∈ Set.range g

lemma mem_jointlySurjectivePrecoverage_iff {X : Type u} {R : Presieve X} :
    R ∈ jointlySurjectivePrecoverage X ↔
      ∀ x : X, ∃ (Y : Type u) (g : Y ⟶ X), R g ∧ x ∈ Set.range g :=
  .rfl

lemma singleton_mem_jointlySurjectivePrecoverage_iff {X Y : Type u} {f : X ⟶ Y} :
    Presieve.singleton f ∈ jointlySurjectivePrecoverage Y ↔ Function.Surjective f := by
  rw [mem_jointlySurjectivePrecoverage_iff]
  refine ⟨fun hf x ↦ ?_, fun hf x ↦ ⟨X, f, ⟨⟩, by simp [hf.range_eq]⟩⟩
  obtain ⟨_, _, ⟨⟩, hx⟩ := hf x
  exact hx
