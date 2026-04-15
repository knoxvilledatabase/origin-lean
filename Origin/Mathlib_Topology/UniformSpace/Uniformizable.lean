/-
Extracted from Topology/UniformSpace/Uniformizable.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Uniformizable Spaces

A topological space is uniformizable (there exists a uniformity that
generates the same topology) iff it is completely regular.

## Main Results

* `UniformSpace.toCompletelyRegularSpace`: Uniform spaces are completely regular
* `CompletelyRegularSpace.exists_uniformSpace`: Completely regular spaces are uniformizable
* `CompletelyRegularSpace.of_exists_uniformSpace`: Uniformizable spaces are completely regular
* `completelyRegularSpace_iff_exists_uniformSpace`: A space is completely regular
  iff it is uniformizable

## Implementation Details

Urysohn's lemma is reused in the proof of `UniformSpace.completelyRegularSpace`.

## References

* <https://www.math.wm.edu/~vinroot/PadicGroups/519probset1.pdf>
-/

variable {X : Type*}

open Filter Set Uniformity UniformSpace SetRel

section UniformSpace

variable [UniformSpace X]

def IsThickening (c u : Set X) :=
  ∃ (x : X) (uc s : SetRel X X),
    IsOpen uc ∧ uc ∈ 𝓤 X ∧ c = closure (ball x uc) ∧
    ball x (s ○ uc ○ s) ⊆ u ∧ s ∈ 𝓤 X

theorem urysohns_main {c u : Set X} (IsThickeningcu : IsThickening c u) :
    ∃ (v : Set X), IsOpen v ∧ c ⊆ v ∧ closure v ⊆ u ∧
      IsThickening c v ∧ IsThickening (closure v) u := by
  obtain ⟨x, uc, s, huc, ucu, rfl, hn, hs⟩ := IsThickeningcu
  obtain ⟨(ds : SetRel X X), hdsu, hdso, -, hdsd⟩ := comp_open_symm_mem_uniformity_sets hs
  have ho : IsOpen (ds ○ uc ○ ds) := (hdso.relComp huc).relComp hdso
  have hsub := calc ds ○ (ds ○ uc ○ ds) ○ ds
    _ = (ds ○ ds) ○ uc ○ (ds ○ ds) := by simp [comp_assoc]
    _ ⊆ s ○ uc ○ s := comp_subset_comp (comp_subset_comp_left hdsd) hdsd
  replace hsub := (ball_mono hsub x).trans hn
  have : ds.IsRefl := id_subset_iff.1 (refl_le_uniformity hdsu)
  refine ⟨ball x (ds ○ uc ○ ds), isOpen_ball x ho, ?_, subset_trans ?_ hsub,
      ⟨x, uc, ds, huc, ucu, rfl, subset_rfl, hdsu⟩,
      ⟨x, ds ○ uc ○ ds, ds, ho, mem_of_superset ucu (right_subset_comp.trans left_subset_comp),
        rfl, hsub, hdsu⟩⟩ <;>
  · refine closure_ball_subset.trans (ball_mono ?_ x)
    rw [closure_eq_inter_uniformity]
    exact iInter₂_subset_of_subset ds hdsu (by simp [comp_assoc])

-- INSTANCE (free from Core): UniformSpace.toCompletelyRegularSpace

end UniformSpace

section TopologicalSpace

variable [t : TopologicalSpace X]

public theorem CompletelyRegularSpace.exists_uniformSpace [CompletelyRegularSpace X] :
    ∃ u : UniformSpace X, u.toTopologicalSpace = t :=
  ⟨uniformSpaceOfCompactR1.comap stoneCechUnit, isInducing_stoneCechUnit.eq_induced.symm⟩

public theorem completelyRegularSpace_iff_exists_uniformSpace :
    CompletelyRegularSpace X ↔ ∃ u : UniformSpace X, u.toTopologicalSpace = t :=
  ⟨(·.exists_uniformSpace), .of_exists_uniformSpace⟩

end TopologicalSpace
