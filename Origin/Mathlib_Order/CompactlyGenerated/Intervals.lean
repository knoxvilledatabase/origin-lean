/-
Extracted from Order/CompactlyGenerated/Intervals.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Results about compactness properties for intervals in complete lattices
-/

variable {ι α : Type*} [CompleteLattice α]

namespace Set.Iic

-- INSTANCE (free from Core): instIsCompactlyGenerated

end Set.Iic

open Set (Iic)

theorem complementedLattice_of_complementedLattice_Iic
    [IsModularLattice α] [IsCompactlyGenerated α]
    {s : Set ι} {f : ι → α}
    (h : ∀ i ∈ s, ComplementedLattice <| Iic (f i))
    (h' : ⨆ i ∈ s, f i = ⊤) :
    ComplementedLattice α := by
  apply complementedLattice_of_sSup_atoms_eq_top
  have : ∀ i ∈ s, ∃ t : Set α, f i = sSup t ∧ ∀ a ∈ t, IsAtom a := fun i hi ↦ by
    replace h := complementedLattice_iff_isAtomistic.mp (h i hi)
    obtain ⟨u, hu, hu'⟩ := eq_sSup_atoms (⊤ : Iic (f i))
    refine ⟨(↑) '' u, ?_, ?_⟩
    · replace hu : f i = ↑(sSup u) := Subtype.ext_iff.mp hu
      simp_rw [hu, Iic.coe_sSup]
    · rintro b ⟨⟨a, ha'⟩, ha, rfl⟩
      exact IsAtom.of_isAtom_coe_Iic (hu' _ ha)
  choose t ht ht' using this
  let u : Set α := ⋃ i, ⋃ hi : i ∈ s, t i hi
  have hu₁ : u ⊆ {a | IsAtom a} := by
    rintro a ⟨-, ⟨i, rfl⟩, ⟨-, ⟨hi, rfl⟩, ha : a ∈ t i hi⟩⟩
    exact ht' i hi a ha
  have hu₂ : sSup u = ⨆ i ∈ s, f i := by simp_rw [u, sSup_iUnion, biSup_congr' ht]
  rw [eq_top_iff, ← h', ← hu₂]
  exact sSup_le_sSup hu₁
