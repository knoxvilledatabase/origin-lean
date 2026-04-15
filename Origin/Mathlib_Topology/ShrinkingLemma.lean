/-
Extracted from Topology/ShrinkingLemma.lean
Genuine: 17 of 20 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Topology.Separation.Basic

/-!
# The shrinking lemma

In this file we prove a few versions of the shrinking lemma. The lemma says that in a normal
topological space a point finite open covering can be “shrunk”: for a point finite open covering
`u : ι → Set X` there exists a refinement `v : ι → Set X` such that `closure (v i) ⊆ u i`.

For finite or countable coverings this lemma can be proved without the axiom of choice, see
[ncatlab](https://ncatlab.org/nlab/show/shrinking+lemma) for details. We only formalize the most
general result that works for any covering but needs the axiom of choice.

We prove two versions of the lemma:

* `exists_subset_iUnion_closure_subset` deals with a covering of a closed set in a normal space;
* `exists_iUnion_eq_closure_subset` deals with a covering of the whole space.

## Tags

normal space, shrinking lemma
-/

open Set Function

noncomputable section

variable {ι X : Type*} [TopologicalSpace X]

namespace ShrinkingLemma

@[ext] structure PartialRefinement (u : ι → Set X) (s : Set X) (p : Set X → Prop) where
  /-- A family of sets that form a partial refinement of `u`. -/
  toFun : ι → Set X
  /-- The set of indexes `i` such that `i`-th set is already shrunk. -/
  carrier : Set ι
  /-- Each set from the partially refined family is open. -/
  protected isOpen : ∀ i, IsOpen (toFun i)
  /-- The partially refined family still covers the set. -/
  subset_iUnion : s ⊆ ⋃ i, toFun i
  /-- For each `i ∈ carrier`, the original set includes the closure of the refined set. -/
  closure_subset : ∀ {i}, i ∈ carrier → closure (toFun i) ⊆ u i
  /-- For each `i ∈ carrier`, the refined set satisfies `p`. -/
  pred_of_mem {i} (hi : i ∈ carrier) : p (toFun i)
  /-- Sets that correspond to `i ∉ carrier` are not modified. -/
  apply_eq : ∀ {i}, i ∉ carrier → toFun i = u i

namespace PartialRefinement

variable {u : ι → Set X} {s : Set X} {p : Set X → Prop}

instance : CoeFun (PartialRefinement u s p) fun _ => ι → Set X := ⟨toFun⟩

protected theorem subset (v : PartialRefinement u s p) (i : ι) : v i ⊆ u i := by
  classical
  exact if h : i ∈ v.carrier then subset_closure.trans (v.closure_subset h) else (v.apply_eq h).le

open Classical in

instance : PartialOrder (PartialRefinement u s p) where
  le v₁ v₂ := v₁.carrier ⊆ v₂.carrier ∧ ∀ i ∈ v₁.carrier, v₁ i = v₂ i
  le_refl _ := ⟨Subset.refl _, fun _ _ => rfl⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨Subset.trans h₁₂.1 h₂₃.1, fun i hi => (h₁₂.2 i hi).trans (h₂₃.2 i <| h₁₂.1 hi)⟩
  le_antisymm v₁ v₂ h₁₂ h₂₁ :=
    have hc : v₁.carrier = v₂.carrier := Subset.antisymm h₁₂.1 h₂₁.1
    PartialRefinement.ext
      (funext fun x =>
        if hx : x ∈ v₁.carrier then h₁₂.2 _ hx
        else (v₁.apply_eq hx).trans (Eq.symm <| v₂.apply_eq <| hc ▸ hx))
      hc

theorem apply_eq_of_chain {c : Set (PartialRefinement u s p)} (hc : IsChain (· ≤ ·) c) {v₁ v₂}
    (h₁ : v₁ ∈ c) (h₂ : v₂ ∈ c) {i} (hi₁ : i ∈ v₁.carrier) (hi₂ : i ∈ v₂.carrier) :
    v₁ i = v₂ i :=
  (hc.total h₁ h₂).elim (fun hle => hle.2 _ hi₁) (fun hle => (hle.2 _ hi₂).symm)

def chainSupCarrier (c : Set (PartialRefinement u s p)) : Set ι :=
  ⋃ v ∈ c, carrier v

open Classical in

def find (c : Set (PartialRefinement u s p)) (ne : c.Nonempty) (i : ι) : PartialRefinement u s p :=
  if hi : ∃ v ∈ c, i ∈ carrier v then hi.choose else ne.some

theorem find_mem {c : Set (PartialRefinement u s p)} (i : ι) (ne : c.Nonempty) :
    find c ne i ∈ c := by
  rw [find]
  split_ifs with h
  exacts [h.choose_spec.1, ne.some_mem]

theorem mem_find_carrier_iff {c : Set (PartialRefinement u s p)} {i : ι} (ne : c.Nonempty) :
    i ∈ (find c ne i).carrier ↔ i ∈ chainSupCarrier c := by
  rw [find]
  split_ifs with h
  · have := h.choose_spec
    exact iff_of_true this.2 (mem_iUnion₂.2 ⟨_, this.1, this.2⟩)
  · push_neg at h
    refine iff_of_false (h _ ne.some_mem) ?_
    simpa only [chainSupCarrier, mem_iUnion₂, not_exists]

theorem find_apply_of_mem {c : Set (PartialRefinement u s p)} (hc : IsChain (· ≤ ·) c)
    (ne : c.Nonempty) {i v} (hv : v ∈ c) (hi : i ∈ carrier v) : find c ne i i = v i :=
  apply_eq_of_chain hc (find_mem _ _) hv ((mem_find_carrier_iff _).2 <| mem_iUnion₂.2 ⟨v, hv, hi⟩)
    hi

def chainSup (c : Set (PartialRefinement u s p)) (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty)
    (hfin : ∀ x ∈ s, { i | x ∈ u i }.Finite) (hU : s ⊆ ⋃ i, u i) : PartialRefinement u s p where
  toFun i := find c ne i i
  carrier := chainSupCarrier c
  isOpen i := (find _ _ _).isOpen i
  subset_iUnion x hxs := mem_iUnion.2 <| by
    rcases em (∃ i, i ∉ chainSupCarrier c ∧ x ∈ u i) with (⟨i, hi, hxi⟩ | hx)
    · use i
      simpa only [(find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)]
    · simp_rw [not_exists, not_and, not_imp_not, chainSupCarrier, mem_iUnion₂] at hx
      haveI : Nonempty (PartialRefinement u s p) := ⟨ne.some⟩
      choose! v hvc hiv using hx
      rcases (hfin x hxs).exists_maximal_wrt v _ (mem_iUnion.1 (hU hxs)) with
        ⟨i, hxi : x ∈ u i, hmax : ∀ j, x ∈ u j → v i ≤ v j → v i = v j⟩
      rcases mem_iUnion.1 ((v i).subset_iUnion hxs) with ⟨j, hj⟩
      use j
      have hj' : x ∈ u j := (v i).subset _ hj
      have : v j ≤ v i := (hc.total (hvc _ hxi) (hvc _ hj')).elim (fun h => (hmax j hj' h).ge) id
      simpa only [find_apply_of_mem hc ne (hvc _ hxi) (this.1 <| hiv _ hj')]
  closure_subset hi := (find c ne _).closure_subset ((mem_find_carrier_iff _).2 hi)
  pred_of_mem {i} hi := by
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hi
    simp only [mem_iUnion, exists_prop] at hv
    simp only
    rw [find_apply_of_mem hc ne hv.1 hv.2]
    exact v.pred_of_mem hv.2
  apply_eq hi := (find c ne _).apply_eq (mt (mem_find_carrier_iff _).1 hi)

theorem le_chainSup {c : Set (PartialRefinement u s p)} (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty)
    (hfin : ∀ x ∈ s, { i | x ∈ u i }.Finite) (hU : s ⊆ ⋃ i, u i) {v} (hv : v ∈ c) :
    v ≤ chainSup c hc ne hfin hU :=
  ⟨fun _ hi => mem_biUnion hv hi, fun _ hi => (find_apply_of_mem hc _ hv hi).symm⟩

theorem exists_gt [NormalSpace X] (v : PartialRefinement u s ⊤) (hs : IsClosed s)
    (i : ι) (hi : i ∉ v.carrier) :
    ∃ v' : PartialRefinement u s ⊤, v < v' := by
  have I : (s ∩ ⋂ (j) (_ : j ≠ i), (v j)ᶜ) ⊆ v i := by
    simp only [subset_def, mem_inter_iff, mem_iInter, and_imp]
    intro x hxs H
    rcases mem_iUnion.1 (v.subset_iUnion hxs) with ⟨j, hj⟩
    exact (em (j = i)).elim (fun h => h ▸ hj) fun h => (H j h hj).elim
  have C : IsClosed (s ∩ ⋂ (j) (_ : j ≠ i), (v j)ᶜ) :=
    IsClosed.inter hs (isClosed_biInter fun _ _ => isClosed_compl_iff.2 <| v.isOpen _)
  rcases normal_exists_closure_subset C (v.isOpen i) I with ⟨vi, ovi, hvi, cvi⟩
  classical
  refine ⟨⟨update v i vi, insert i v.carrier, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    rcases eq_or_ne j i with (rfl| hne) <;> simp [*, v.isOpen]
  · refine fun x hx => mem_iUnion.2 ?_
    rcases em (∃ j ≠ i, x ∈ v j) with (⟨j, hji, hj⟩ | h)
    · use j
      rwa [update_noteq hji]
    · push_neg at h
      use i
      rw [update_same]
      exact hvi ⟨hx, mem_biInter h⟩
  · rintro j (rfl | hj)
    · rwa [update_same, ← v.apply_eq hi]
    · rw [update_noteq (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · exact fun _ => trivial
  · intro j hj
    rw [mem_insert_iff, not_or] at hj
    rw [update_noteq hj.1, v.apply_eq hj.2]
  · refine ⟨subset_insert _ _, fun j hj => ?_⟩
    exact (update_noteq (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)

end PartialRefinement

end ShrinkingLemma

section NormalSpace

open ShrinkingLemma

variable {u : ι → Set X} {s : Set X} [NormalSpace X]

theorem exists_subset_iUnion_closure_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i := by
  haveI : Nonempty (PartialRefinement u s ⊤) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : ∀ c : Set (PartialRefinement u s ⊤),
      IsChain (· ≤ ·) c → c.Nonempty → ∃ ub, ∀ v ∈ c, v ≤ ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices ∀ i, i ∈ v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i)⟩
  refine fun i ↦ by_contra fun hi ↦ ?_
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩
  exact hv.not_lt hlt

theorem exists_subset_iUnion_closed_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset hs uo uf us
  ⟨fun i => closure (v i), Subset.trans hsv (iUnion_mono fun _ => subset_closure),
    fun _ => isClosed_closure, hv⟩

theorem exists_iUnion_eq_closure_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : ⋃ i, u i = univ) :
    ∃ v : ι → Set X, iUnion v = univ ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_iUnion_closure_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

theorem exists_iUnion_eq_closed_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : ⋃ i, u i = univ) :
    ∃ v : ι → Set X, iUnion v = univ ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_iUnion_closed_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

end NormalSpace

section T2LocallyCompactSpace

open ShrinkingLemma

variable {u : ι → Set X} {s : Set X} [T2Space X] [LocallyCompactSpace X]

theorem exists_gt_t2space (v : PartialRefinement u s (fun w => IsCompact (closure w)))
    (hs : IsCompact s) (i : ι) (hi : i ∉ v.carrier) :
    ∃ v' : PartialRefinement u s (fun w => IsCompact (closure w)),
      v < v' ∧ IsCompact (closure (v' i)) := by
  -- take `v i` such that `closure (v i)` is compact
  set si := s ∩ (⋃ j ≠ i, v j)ᶜ with hsi
  simp only [ne_eq, compl_iUnion] at hsi
  have hsic : IsCompact si := by
    apply IsCompact.of_isClosed_subset hs _ Set.inter_subset_left
    · have : IsOpen (⋃ j ≠ i, v j) := by
        apply isOpen_biUnion
        intro j _
        exact v.isOpen j
      exact IsClosed.inter (IsCompact.isClosed hs) (IsOpen.isClosed_compl this)
  have : si ⊆ v i := by
    intro x hx
    have (j) (hj : j ≠ i) : x ∉ v j := by
      rw [hsi] at hx
      apply Set.not_mem_of_mem_compl
      have hsi' : x ∈ (⋂ i_1, ⋂ (_ : ¬i_1 = i), (v.toFun i_1)ᶜ) := Set.mem_of_mem_inter_right hx
      rw [ne_eq] at hj
      rw [Set.mem_iInter₂] at hsi'
      exact hsi' j hj
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
      (v.subset_iUnion (Set.mem_of_mem_inter_left hx))
    obtain rfl : j = i := by
      by_contra! h
      exact this j h hj
    exact hj
  obtain ⟨vi, hvi⟩ := exists_open_between_and_isCompact_closure hsic (v.isOpen i) this
  classical
  refine ⟨⟨update v i vi, insert i v.carrier, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro j
    rcases eq_or_ne j i with (rfl| hne) <;> simp [*, v.isOpen]
  · refine fun x hx => mem_iUnion.2 ?_
    rcases em (∃ j ≠ i, x ∈ v j) with (⟨j, hji, hj⟩ | h)
    · use j
      rwa [update_noteq hji]
    · push_neg at h
      use i
      rw [update_same]
      apply hvi.2.1
      rw [hsi]
      exact ⟨hx, mem_iInter₂_of_mem h⟩
  · rintro j (rfl | hj)
    · rw [update_same]
      exact subset_trans hvi.2.2.1 <| PartialRefinement.subset v j
    · rw [update_noteq (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · intro j hj
    rw [mem_insert_iff] at hj
    by_cases h : j = i
    · rw [← h]
      simp only [update_same]
      exact hvi.2.2.2
    · apply hj.elim
      · intro hji
        exact False.elim (h hji)
      · intro hjmemv
        rw [update_noteq h]
        exact v.pred_of_mem hjmemv
  · intro j hj
    rw [mem_insert_iff, not_or] at hj
    rw [update_noteq hj.1, v.apply_eq hj.2]
  · refine ⟨subset_insert _ _, fun j hj => ?_⟩
    exact (update_noteq (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)
  · simp only [update_same]
    exact hvi.2.2.2

theorem exists_subset_iUnion_closure_subset_t2space (hs : IsCompact s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsOpen (v i)) ∧ (∀ i, closure (v i) ⊆ u i)
      ∧ (∀ i, IsCompact (closure (v i))) := by
  haveI : Nonempty (PartialRefinement u s (fun w => IsCompact (closure w))) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : ∀ c : Set (PartialRefinement u s (fun w => IsCompact (closure w))),
      IsChain (· ≤ ·) c → c.Nonempty → ∃ ub, ∀ v ∈ c, v ≤ ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices ∀ i, i ∈ v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i), ?_⟩
  · intro i
    exact v.pred_of_mem (this i)
  · intro i
    by_contra! hi
    rcases exists_gt_t2space v hs i hi with ⟨v', hlt, _⟩
    exact hv.not_lt hlt

theorem exists_subset_iUnion_compact_subset_t2space (hs : IsCompact s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsClosed (v i)) ∧ (∀ i, v i ⊆ u i)
      ∧ ∀ i, IsCompact (v i) := by
  let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset_t2space hs uo uf us
  use fun i => closure (v i)
  refine ⟨?_, ?_, ?_⟩
  · exact Subset.trans hsv (iUnion_mono fun _ => subset_closure)
  · simp only [isClosed_closure, implies_true]
  · simp only
    exact And.intro (fun i => hv.1 i) (fun i => hv.2 i)

end T2LocallyCompactSpace
