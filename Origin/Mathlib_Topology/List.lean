/-
Extracted from Topology/List.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Topology on lists and vectors

-/

open TopologicalSpace Set Filter

open Topology

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

-- INSTANCE (free from Core): :

theorem nhds_list (as : List α) : 𝓝 as = traverse 𝓝 as := by
  refine nhds_mkOfNhds _ _ ?_ ?_
  · intro l
    induction l with
    | nil => exact le_rfl
    | cons a l ih =>
      suffices List.cons <$> pure a <*> pure l ≤ List.cons <$> 𝓝 a <*> traverse 𝓝 l by
        simpa only [functor_norm] using this
      exact Filter.seq_mono (Filter.map_mono <| pure_le_nhds a) ih
  · intro l s hs
    rcases (mem_traverse_iff _ _).1 hs with ⟨u, hu, hus⟩
    clear as hs
    have : ∃ v : List (Set α), l.Forall₂ (fun a s => IsOpen s ∧ a ∈ s) v ∧ sequence v ⊆ s := by
      induction hu generalizing s with
      | nil =>
        exists []
        simp only [List.forall₂_nil_left_iff]
        exact ⟨trivial, hus⟩
      | cons ht _ ih =>
        rcases mem_nhds_iff.1 ht with ⟨u, hut, hu⟩
        rcases ih _ Subset.rfl with ⟨v, hv, hvss⟩
        exact
          ⟨u::v, List.Forall₂.cons hu hv,
            Subset.trans (Set.seq_mono (Set.image_mono hut) hvss) hus⟩
    rcases this with ⟨v, hv, hvs⟩
    have : sequence v ∈ traverse 𝓝 l :=
      mem_traverse _ _ <| hv.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha
    refine mem_of_superset this fun u hu ↦ ?_
    have hu := (List.mem_traverse _ _).1 hu
    have : List.Forall₂ (fun a s => IsOpen s ∧ a ∈ s) u v := by
      refine List.Forall₂.flip ?_
      replace hv := hv.flip
      simp only [List.forall₂_and_left, Function.flip_def] at hv ⊢
      exact ⟨hv.1, hu.flip⟩
    grw [← hvs]
    exact mem_traverse _ _ (this.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha)
