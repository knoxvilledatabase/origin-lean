/-
Extracted from Topology/Baire/LocallyCompactRegular.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Second Baire theorem

In this file we prove that a locally compact regular topological space has Baire property.
-/

open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X] {s : Set X} [R1Space X] [LocallyCompactSpace X]

-- INSTANCE (free from Core): (priority

theorem IsGδ.of_t2Space_locallyCompactSpace (hG : IsGδ s) : BaireSpace s := by
  have : BaireSpace (closure s) := by
    convert BaireSpace.of_t2Space_locallyCompactSpace using 1
    · infer_instance
    · exact isClosed_closure.locallyCompactSpace
  have : BaireSpace ((↑) ⁻¹' s : Set (closure s)) :=
    (isGδ_induced continuous_subtype_val hG).baireSpace_of_dense
    (by simp [Subtype.dense_iff, inter_eq_right.mpr subset_closure])
  have h_homeo : Homeomorph ((↑) ⁻¹' s : Set (closure s)) s := ⟨⟨fun x => ⟨x, x.2⟩,
    fun x => ⟨⟨x, subset_closure x.2⟩, x.2⟩, by grind, by grind⟩, by fun_prop, by fun_prop⟩
  exact h_homeo.baireSpace
