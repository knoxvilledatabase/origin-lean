/-
Extracted from Order/CompactlyGenerated/Basic.lean
Genuine: 21 of 24 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Compactness properties for complete lattices

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define three especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
* `CompleteLattice.IsSupClosedCompact`
* `CompleteLattice.IsSupFiniteCompact`
* `IsCompactElement`
* `IsCompactlyGenerated`

## Main results
The main result is that the following four conditions are equivalent for a complete lattice:
* `well_founded (>)`
* `CompleteLattice.IsSupClosedCompact`
* `CompleteLattice.IsSupFiniteCompact`
* `∀ k, IsCompactElement k`

This is demonstrated by means of the following four lemmas:
* `CompleteLattice.WellFounded.isSupFiniteCompact`
* `CompleteLattice.IsSupFiniteCompact.isSupClosedCompact`
* `CompleteLattice.IsSupClosedCompact.wellFounded`
* `CompleteLattice.isSupFiniteCompact_iff_all_elements_compact`

We also show well-founded lattices are compactly generated
(`CompleteLattice.isCompactlyGenerated_of_wellFounded`).

## References
- [G. Călugăreanu, *Lattice Concepts of Module Theory*][calugareanu]

## Tags

complete lattice, well-founded, compact
-/

open Set

def IsCompactElement {α : Type*} [PartialOrder α] (k : α) :=
  ∀ (s : Set α) (u : α),
    s.Nonempty →
    DirectedOn (· ≤ ·) s →
    IsLUB s u →
    k ≤ u →
    ∃ x ∈ s, k ≤ x

variable {ι : Sort*} {α : Type*} [CompleteLattice α] {f : ι → α}

namespace CompleteLattice

variable (α)

def IsSupClosedCompact : Prop :=
  ∀ (s : Set α) (_ : s.Nonempty), SupClosed s → sSup s ∈ s

def IsSupFiniteCompact : Prop :=
  ∀ s : Set α, ∃ t : Finset α, ↑t ⊆ s ∧ sSup s = t.sup id

theorem isCompactElement_iff_le_of_directed_sSup_le (k : α) :
    IsCompactElement k ↔
      ∀ s : Set α, s.Nonempty → DirectedOn (· ≤ ·) s → k ≤ sSup s → ∃ x : α, x ∈ s ∧ k ≤ x := by
  constructor
  · intro hk s hs hs' h_le
    exact hk s (sSup s) hs hs' (isLUB_sSup s) h_le
  · intro h s u hs hs' hu h_le
    rw [isLUB_iff_sSup_eq] at hu
    rw [← hu] at h_le
    exact h s hs hs' h_le

theorem isCompactElement_iff_exists_le_sSup_of_le_sSup (k : α) :
    IsCompactElement k ↔ ∀ s : Set α, k ≤ sSup s → ∃ t : Finset α, ↑t ⊆ s ∧ k ≤ t.sup id := by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le]
    constructor
    · intro hk s hsup
      -- Consider the set of finite joins of elements of the (plain) set s.
      let S : Set α := { x | ∃ t : Finset α, ↑t ⊆ s ∧ x = t.sup id }
      -- S is directed, nonempty, and still has sup above k.
      have dir_US : DirectedOn (· ≤ ·) S := by
        rintro x ⟨c, hc⟩ y ⟨d, hd⟩
        use x ⊔ y
        constructor
        · use c ∪ d
          constructor
          · simp only [hc.left, hd.left, Set.union_subset_iff, Finset.coe_union, and_self_iff]
          · simp only [hc.right, hd.right, Finset.sup_union]
        simp only [and_self_iff, le_sup_left, le_sup_right]
      have sup_S : sSup s ≤ sSup S := by
        apply sSup_le_sSup
        intro x hx
        use {x}
        simpa only [and_true, id, Finset.coe_singleton, eq_self_iff_true,
          Finset.sup_singleton, Set.singleton_subset_iff]
      have Sne : S.Nonempty := by
        suffices ⊥ ∈ S from Set.nonempty_of_mem this
        use ∅
        simp
      -- Now apply the defn of compact and finish.
      obtain ⟨j, ⟨hjS, hjk⟩⟩ := hk S Sne dir_US (le_trans hsup sup_S)
      obtain ⟨t, ⟨htS, htsup⟩⟩ := hjS
      use t
      exact ⟨htS, by rwa [← htsup]⟩
    · intro hk s hne hdir hsup
      obtain ⟨t, ht⟩ := hk s hsup
      -- certainly every element of t is below something in s, since ↑t ⊆ s.
      have t_below_s : ∀ x ∈ t, ∃ y ∈ s, x ≤ y := fun x hxt => ⟨x, ht.left hxt, le_rfl⟩
      obtain ⟨x, ⟨hxs, hsupx⟩⟩ := Finset.sup_le_of_le_directed s hne hdir t t_below_s
      exact ⟨x, ⟨hxs, le_trans ht.right hsupx⟩⟩

theorem isCompactElement_iff_exists_le_iSup_of_le_iSup.{u} {α : Type u} [CompleteLattice α]
    (k : α) : IsCompactElement k ↔
      ∀ (ι : Type u) (s : ι → α), k ≤ iSup s → ∃ t : Finset ι, k ≤ t.sup s := by
  classical
    rw [isCompactElement_iff_exists_le_sSup_of_le_sSup]
    constructor
    · intro H ι s hs
      obtain ⟨t, ht, ht'⟩ := H (Set.range s) hs
      have : ∀ x : t, ∃ i, s i = x := fun x => ht x.prop
      choose f hf using this
      refine ⟨Finset.univ.image f, ht'.trans ?_⟩
      rw [Finset.sup_le_iff]
      intro b hb
      rw [← show s (f ⟨b, hb⟩) = id b from hf _]
      exact Finset.le_sup (Finset.mem_image_of_mem f <| Finset.mem_univ (Subtype.mk b hb))
    · intro H s hs
      obtain ⟨t, ht⟩ :=
        H s Subtype.val
          (by
            delta iSup
            rwa [Subtype.range_coe])
      refine ⟨t.image Subtype.val, by simp, ht.trans ?_⟩
      rw [Finset.sup_le_iff]
      exact fun x hx => @Finset.le_sup _ _ _ _ _ id _ (Finset.mem_image_of_mem Subtype.val hx)

theorem IsCompactElement.directed_sSup_lt_of_lt {α : Type*} [CompleteLattice α] {k : α}
    (hk : IsCompactElement k) {s : Set α} (hemp : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hbelow : ∀ x ∈ s, x < k) : sSup s < k := by
  rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
  by_contra h
  have sSup' : sSup s ≤ k := sSup_le fun s hs => (hbelow s hs).le
  replace sSup : sSup s = k := eq_iff_le_not_lt.mpr ⟨sSup', h⟩
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le
  obtain hxk := hbelow x hxs
  exact hxk.ne (hxk.le.antisymm hkx)

theorem isCompactElement_finsetSup {α β : Type*} [CompleteLattice α] {f : β → α} (s : Finset β)
    (h : ∀ x ∈ s, IsCompactElement (f x)) : IsCompactElement (s.sup f) := by
  classical
    simp_rw [isCompactElement_iff_le_of_directed_sSup_le] at ⊢ h
    intro d hemp hdir hsup
    rw [← Function.id_comp f]
    rw [← Finset.sup_image]
    apply Finset.sup_le_of_le_directed d hemp hdir
    rintro x hx
    obtain ⟨p, ⟨hps, rfl⟩⟩ := Finset.mem_image.mp hx
    specialize h p hps
    specialize h d hemp hdir (le_trans (Finset.le_sup hps) hsup)
    simpa only [exists_prop]

theorem WellFoundedGT.isSupFiniteCompact [WellFoundedGT α] :
    IsSupFiniteCompact α := fun s => by
  let S := { x | ∃ t : Finset α, ↑t ⊆ s ∧ t.sup id = x }
  obtain ⟨m, ⟨t, ⟨ht₁, rfl⟩⟩, hm⟩ := wellFounded_gt.has_min S ⟨⊥, ∅, by simp⟩
  refine ⟨t, ht₁, (sSup_le fun y hy => ?_).antisymm ?_⟩
  · classical
    rw [eq_of_le_of_not_lt (Finset.sup_mono (t.subset_insert y))
        (hm _ ⟨insert y t, by simp [Set.insert_subset_iff, hy, ht₁]⟩)]
    simp
  · rw [Finset.sup_id_eq_sSup]
    exact sSup_le_sSup ht₁

theorem IsSupClosedCompact.wellFoundedGT (h : IsSupClosedCompact α) :
    WellFoundedGT α where
  wf := by
    refine RelEmbedding.wellFounded_iff_isEmpty.mpr ⟨fun a => ?_⟩
    suffices sSup (Set.range a) ∈ Set.range a by
      obtain ⟨n, hn⟩ := Set.mem_range.mp this
      have h' : sSup (Set.range a) < a (n + 1) := by
        change _ > _
        simp [← hn, a.map_rel_iff]
      apply lt_irrefl (a (n + 1))
      apply lt_of_le_of_lt _ h'
      apply le_sSup
      apply Set.mem_range_self
    apply h (Set.range a)
    · use a 37
      apply Set.mem_range_self
    · rintro x ⟨m, hm⟩ y ⟨n, hn⟩
      use m ⊔ n
      rw [← hm, ← hn]
      apply RelHomClass.map_sup a

open List in

theorem wellFoundedGT_characterisations : List.TFAE
    [WellFoundedGT α, IsSupFiniteCompact α, IsSupClosedCompact α, ∀ k : α, IsCompactElement k] := by
  tfae_have 1 → 2 := @WellFoundedGT.isSupFiniteCompact α _
  tfae_have 2 → 3 := IsSupFiniteCompact.isSupClosedCompact α
  tfae_have 3 → 1 := IsSupClosedCompact.wellFoundedGT α
  tfae_have 2 ↔ 4 := isSupFiniteCompact_iff_all_elements_compact α
  tfae_finish

theorem wellFoundedGT_iff_isSupFiniteCompact :
    WellFoundedGT α ↔ IsSupFiniteCompact α :=
  (wellFoundedGT_characterisations α).out 0 1

theorem isSupFiniteCompact_iff_isSupClosedCompact : IsSupFiniteCompact α ↔ IsSupClosedCompact α :=
  (wellFoundedGT_characterisations α).out 1 2

theorem isSupClosedCompact_iff_wellFoundedGT :
    IsSupClosedCompact α ↔ WellFoundedGT α :=
  (wellFoundedGT_characterisations α).out 2 0

alias ⟨_, IsSupFiniteCompact.wellFoundedGT⟩ := wellFoundedGT_iff_isSupFiniteCompact

alias ⟨_, IsSupClosedCompact.isSupFiniteCompact⟩ := isSupFiniteCompact_iff_isSupClosedCompact

alias ⟨_, WellFoundedGT.isSupClosedCompact⟩ := isSupClosedCompact_iff_wellFoundedGT

end CompleteLattice

theorem WellFoundedGT.finite_of_sSupIndep [WellFoundedGT α] {s : Set α}
    (hs : sSupIndep s) : s.Finite := by
  classical
    by_contra! contra
    obtain ⟨t, ht₁, ht₂⟩ := CompleteLattice.WellFoundedGT.isSupFiniteCompact α s
    replace contra : ∃ x : α, x ∈ s ∧ x ≠ ⊥ ∧ x ∉ t := by
      have : (s \ (insert ⊥ t : Finset α)).Infinite := contra.diff (Finset.finite_toSet _)
      obtain ⟨x, hx₁, hx₂⟩ := this.nonempty
      exact ⟨x, hx₁, by simpa [not_or] using hx₂⟩
    obtain ⟨x, hx₀, hx₁, hx₂⟩ := contra
    replace hs : x ⊓ sSup s = ⊥ := by
      have := hs.mono (by simp [ht₁, hx₀, -Set.union_singleton] : ↑t ∪ {x} ≤ s) (by simp : x ∈ _)
      simpa [Disjoint, hx₂, ← t.sup_id_eq_sSup, ← ht₂] using this.eq_bot
    apply hx₁
    rw [← hs, eq_comm, inf_eq_left]
    exact le_sSup hx₀

theorem WellFoundedGT.finite_ne_bot_of_iSupIndep [WellFoundedGT α]
    {ι : Type*} {t : ι → α} (ht : iSupIndep t) : Set.Finite {i | t i ≠ ⊥} := by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range

theorem WellFoundedGT.finite_of_iSupIndep [WellFoundedGT α] {ι : Type*}
    {t : ι → α} (ht : iSupIndep t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Finite ι :=
  haveI := (WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

theorem WellFoundedLT.finite_of_sSupIndep [WellFoundedLT α] {s : Set α}
    (hs : sSupIndep s) : s.Finite := by
  by_contra inf
  let e := (Infinite.diff inf <| finite_singleton ⊥).to_subtype.natEmbedding
  let a n := ⨆ i ≥ n, (e i).1
  have sup_le n : (e n).1 ⊔ a (n + 1) ≤ a n := sup_le_iff.mpr ⟨le_iSup₂_of_le n le_rfl le_rfl,
    iSup₂_le fun i hi ↦ le_iSup₂_of_le i (n.le_succ.trans hi) le_rfl⟩
  have lt n : a (n + 1) < a n := (Disjoint.right_lt_sup_of_left_ne_bot
    ((hs (e n).2.1).mono_right <| iSup₂_le fun i hi ↦ le_sSup ?_) (e n).2.2).trans_le (sup_le n)
  · exact (RelEmbedding.natGT a lt).not_wellFounded wellFounded_lt
  exact ⟨(e i).2.1, fun h ↦ n.lt_succ_self.not_ge <| hi.trans_eq <| e.2 <| Subtype.val_injective h⟩

theorem WellFoundedLT.finite_ne_bot_of_iSupIndep [WellFoundedLT α]
    {ι : Type*} {t : ι → α} (ht : iSupIndep t) : Set.Finite {i | t i ≠ ⊥} := by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range

theorem WellFoundedLT.finite_of_iSupIndep [WellFoundedLT α] {ι : Type*}
    {t : ι → α} (ht : iSupIndep t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Finite ι :=
  haveI := (WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

class IsCompactlyGenerated (α : Type*) [CompleteLattice α] : Prop where
  /-- In a compactly generated complete lattice,
  every element is the `sSup` of some set of compact elements. -/
  exists_sSup_eq : ∀ x : α, ∃ s : Set α, (∀ x ∈ s, IsCompactElement x) ∧ sSup s = x

variable [IsCompactlyGenerated α] {a : α} {s : Set α}
