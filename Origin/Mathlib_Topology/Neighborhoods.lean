/-
Extracted from Topology/Neighborhoods.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Neighborhoods in topological spaces

Each point `x` of `X` gets a neighborhood filter `𝓝 x`.

## Tags

neighborhood
-/

open Set Filter Topology

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Sort v} {α : Type*} {x : X} {s t : Set X}

theorem nhds_def' (x : X) : 𝓝 x = ⨅ (s : Set X) (_ : IsOpen s) (_ : x ∈ s), 𝓟 s := by
  simp only [nhds_def, mem_setOf_eq, @and_comm (x ∈ _), iInf_and]

theorem nhds_basis_opens (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsOpen s) fun s => s := by
  rw [nhds_def]
  exact hasBasis_biInf_principal
    (fun s ⟨has, hs⟩ t ⟨hat, ht⟩ =>
      ⟨s ∩ t, ⟨⟨has, hat⟩, IsOpen.inter hs ht⟩, ⟨inter_subset_left, inter_subset_right⟩⟩)
    ⟨univ, ⟨mem_univ x, isOpen_univ⟩⟩

theorem nhds_basis_closeds (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∉ s ∧ IsClosed s) compl :=
  ⟨fun t => (nhds_basis_opens x).mem_iff.trans <|
    compl_surjective.exists.trans <| by simp only [isOpen_compl_iff, mem_compl_iff]⟩
