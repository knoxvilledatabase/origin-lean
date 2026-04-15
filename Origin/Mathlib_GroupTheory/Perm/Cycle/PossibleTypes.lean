/-
Extracted from GroupTheory/Perm/Cycle/PossibleTypes.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Possible cycle types of permutations

* For `m : Multiset ℕ`, `Equiv.Perm.exists_with_cycleType_iff m`
  proves that there are permutations with cycleType `m` if and only if
  its sum is at most `Fintype.card α` and its members are at least 2.

-/

variable (α : Type*) [DecidableEq α] [Fintype α]

section Ranges

theorem List.exists_pw_disjoint_with_card {α : Type*} [Fintype α]
    {c : List ℕ} (hc : c.sum ≤ Fintype.card α) :
    ∃ o : List (List α),
      o.map length = c ∧ (∀ s ∈ o, s.Nodup) ∧ Pairwise List.Disjoint o := by
  let klift (n : ℕ) (hn : n < Fintype.card α) : Fin (Fintype.card α) :=
    (⟨n, hn⟩ : Fin (Fintype.card α))
  let klift' (l : List ℕ) (hl : ∀ a ∈ l, a < Fintype.card α) :
    List (Fin (Fintype.card α)) := List.pmap klift l hl
  have hc'_lt : ∀ l ∈ c.ranges, ∀ n ∈ l, n < Fintype.card α := by
    intro l hl n hn
    apply lt_of_lt_of_le _ hc
    rw [← mem_mem_ranges_iff_lt_sum]
    exact ⟨l, hl, hn⟩
  let l := (ranges c).pmap klift' hc'_lt
  have hl : ∀ (a : List ℕ) (ha : a ∈ c.ranges),
    (klift' a (hc'_lt a ha)).map Fin.valEmbedding = a := by
    intro a ha
    conv_rhs => rw [← List.map_id a]
    rw [List.map_pmap]
    simp [klift, Fin.valEmbedding_apply, List.pmap_eq_map, List.map_id']
  use l.map (List.map (Fintype.equivFin α).symm)
  constructor
  · -- length
    rw [← ranges_length c]
    simp only [l, klift', map_pmap, length_pmap,
      pmap_eq_map]
  constructor
  · -- nodup
    intro s
    rw [mem_map]
    rintro ⟨t, ht, rfl⟩
    apply Nodup.map (Equiv.injective _)
    obtain ⟨u, hu, rfl⟩ := mem_pmap.mp ht
    apply Nodup.of_map
    rw [hl u hu]
    exact ranges_nodup hu
  · -- pairwise disjoint
    refine Pairwise.map _ (fun s t ↦ disjoint_map (Equiv.injective _)) ?_
    -- List.Pairwise List.disjoint l
    apply Pairwise.pmap (List.ranges_disjoint c)
    intro u hu v hv huv
    apply disjoint_pmap
    · intro a a' ha ha' h
      simpa only [klift, Fin.mk_eq_mk] using h
    exact huv

end Ranges
