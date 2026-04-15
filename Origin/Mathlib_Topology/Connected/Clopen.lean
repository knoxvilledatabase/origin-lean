/-
Extracted from Topology/Connected/Clopen.lean
Genuine: 31 of 32 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Connected subsets and their relation to clopen sets

In this file we show how connected subsets of a topological space are intimately connected
to clopen sets.

## Main declarations

+ `IsClopen.biUnion_connectedComponent_eq`: a clopen set is the union of its connected components.
+ `PreconnectedSpace.induction₂`: an induction principle for preconnected spaces.
+ `ConnectedComponents`: The connected components of a topological space, as a quotient type.

-/

open Set Function Topology TopologicalSpace Relation

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section Preconnected

theorem IsPreconnected.subset_isClopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t)
    (hne : (s ∩ t).Nonempty) : s ⊆ t :=
  hs.subset_left_of_subset_union ht.isOpen ht.compl.isOpen disjoint_compl_right (by simp) hne

theorem Sigma.isConnected_iff [∀ i, TopologicalSpace (X i)] {s : Set (Σ i, X i)} :
    IsConnected s ↔ ∃ i t, IsConnected t ∧ s = Sigma.mk i '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨⟨i, x⟩, hx⟩ := hs.nonempty
    have : s ⊆ range (Sigma.mk i) :=
      hs.isPreconnected.subset_isClopen isClopen_range_sigmaMk ⟨⟨i, x⟩, hx, x, rfl⟩
    exact ⟨i, Sigma.mk i ⁻¹' s, hs.preimage_of_isOpenMap sigma_mk_injective isOpenMap_sigmaMk this,
      (Set.image_preimage_eq_of_subset this).symm⟩
  · rintro ⟨i, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

theorem Sigma.isPreconnected_iff [hι : Nonempty ι] [∀ i, TopologicalSpace (X i)]
    {s : Set (Σ i, X i)} : IsPreconnected s ↔ ∃ i t, IsPreconnected t ∧ s = Sigma.mk i '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact ⟨Classical.choice hι, ∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
      exact ⟨a, t, ht.isPreconnected, rfl⟩
  · rintro ⟨a, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

theorem Sum.isConnected_iff [TopologicalSpace β] {s : Set (α ⊕ β)} :
    IsConnected s ↔
      (∃ t, IsConnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsConnected t ∧ s = Sum.inr '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨x | x, hx⟩ := hs.nonempty
    · have h : s ⊆ range Sum.inl :=
        hs.isPreconnected.subset_isClopen isClopen_range_inl ⟨.inl x, hx, x, rfl⟩
      refine Or.inl ⟨Sum.inl ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inl_injective isOpenMap_inl h
      · exact (image_preimage_eq_of_subset h).symm
    · have h : s ⊆ range Sum.inr :=
        hs.isPreconnected.subset_isClopen isClopen_range_inr ⟨.inr x, hx, x, rfl⟩
      refine Or.inr ⟨Sum.inr ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inr_injective isOpenMap_inr h
      · exact (image_preimage_eq_of_subset h).symm
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

theorem Sum.isPreconnected_iff [TopologicalSpace β] {s : Set (α ⊕ β)} :
    IsPreconnected s ↔
      (∃ t, IsPreconnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsPreconnected t ∧ s = Sum.inr '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact Or.inl ⟨∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isConnected_iff.1 ⟨h, hs⟩
    · exact Or.inl ⟨t, ht.isPreconnected, rfl⟩
    · exact Or.inr ⟨t, ht.isPreconnected, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

theorem Continuous.exists_lift_sigma [ConnectedSpace α] [∀ i, TopologicalSpace (X i)]
    {f : α → Σ i, X i} (hf : Continuous f) :
    ∃ (i : ι) (g : α → X i), Continuous g ∧ f = Sigma.mk i ∘ g := by
  obtain ⟨i, hi⟩ : ∃ i, range f ⊆ range (.mk i) := by
    rcases Sigma.isConnected_iff.1 (isConnected_range hf) with ⟨i, s, -, hs⟩
    exact ⟨i, hs.trans_subset (image_subset_range _ _)⟩
  rcases range_subset_range_iff_exists_comp.1 hi with ⟨g, rfl⟩
  refine ⟨i, g, ?_, rfl⟩
  rwa [← IsEmbedding.sigmaMk.continuous_iff] at hf

theorem nonempty_inter [PreconnectedSpace α] {s t : Set α} :
    IsOpen s → IsOpen t → s ∪ t = univ → s.Nonempty → t.Nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using @PreconnectedSpace.isPreconnected_univ α _ _ s t

theorem isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen s ↔ s = ∅ ∨ s = univ :=
  ⟨fun hs =>
    by_contradiction fun h =>
      have h1 : s.Nonempty ∧ sᶜ.Nonempty := by simpa [nonempty_iff_ne_empty] using h
      have ⟨_, h2, h3⟩ := nonempty_inter hs.2 hs.1.isOpen_compl (union_compl_self s) h1.1 h1.2
      h3 h2,
    by rintro (rfl | rfl); exacts [isClopen_empty, isClopen_univ]⟩

theorem IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h' : IsClopen s) (h : s.Nonempty) :
    s = univ :=
  (isClopen_iff.mp h').resolve_left h.ne_empty

open Set.Notation in

lemma isClopen_preimage_val {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hu : IsOpen u) (huv : Disjoint (frontier u) v) : IsClopen (v ↓∩ u) := by
  refine ⟨?_, isOpen_induced hu (f := Subtype.val)⟩
  refine isClosed_induced_iff.mpr ⟨closure u, isClosed_closure, ?_⟩
  apply image_val_injective
  simp only [Subtype.image_preimage_coe]
  rw [closure_eq_self_union_frontier, inter_union_distrib_left, inter_comm _ (frontier u),
    huv.inter_eq, union_empty]

section disjoint_subsets

variable [PreconnectedSpace α]
  {s : ι → Set α} (h_nonempty : ∀ i, (s i).Nonempty) (h_disj : Pairwise (Disjoint on s))

include h_nonempty h_disj

lemma subsingleton_of_disjoint_isClopen
    (h_clopen : ∀ i, IsClopen (s i)) :
    Subsingleton ι := by
  rw [← not_nontrivial_iff_subsingleton]
  by_contra ⟨i, j, h_ne⟩
  replace h_ne : s i ∩ s j = ∅ := by
    simpa only [← bot_eq_empty, eq_bot_iff, ← inf_eq_inter, ← disjoint_iff_inf_le] using h_disj h_ne
  rcases isClopen_iff.mp (h_clopen i) with hi | hi
  · exact (h_nonempty i).ne_empty hi
  · rw [hi, univ_inter] at h_ne
    exact (h_nonempty j).ne_empty h_ne

lemma subsingleton_of_disjoint_isOpen_iUnion_eq_univ
    (h_open : ∀ i, IsOpen (s i)) (h_Union : ⋃ i, s i = univ) :
    Subsingleton ι := by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i ↦ ⟨?_, h_open i⟩)
  rw [← isOpen_compl_iff, compl_eq_univ_diff, ← h_Union, iUnion_diff]
  refine isOpen_iUnion (fun j ↦ ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_open j

lemma subsingleton_of_disjoint_isClosed_iUnion_eq_univ [Finite ι]
    (h_closed : ∀ i, IsClosed (s i)) (h_Union : ⋃ i, s i = univ) :
    Subsingleton ι := by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i ↦ ⟨h_closed i, ?_⟩)
  rw [← isClosed_compl_iff, compl_eq_univ_diff, ← h_Union, iUnion_diff]
  refine isClosed_iUnion_of_finite (fun j ↦ ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_closed j

end disjoint_subsets

theorem frontier_eq_empty_iff [PreconnectedSpace α] {s : Set α} :
    frontier s = ∅ ↔ s = ∅ ∨ s = univ :=
  isClopen_iff_frontier_eq_empty.symm.trans isClopen_iff

theorem nonempty_frontier_iff [PreconnectedSpace α] {s : Set α} :
    (frontier s).Nonempty ↔ s.Nonempty ∧ s ≠ univ := by
  simp only [nonempty_iff_ne_empty, Ne, frontier_eq_empty_iff, not_or]

lemma PreconnectedSpace.induction₂' [PreconnectedSpace α] (P : α → α → Prop)
    (h : ∀ x, ∀ᶠ y in 𝓝 x, P x y ∧ P y x) (h' : IsTrans α P) (x y : α) :
    P x y := by
  let u := {z | P x z}
  have A : IsClosed u := by
    apply isClosed_iff_nhds.2 (fun z hz ↦ ?_)
    rcases hz _ (h z) with ⟨t, ht, h't⟩
    exact h'.trans x t z h't ht.2
  have B : IsOpen u := by
    apply isOpen_iff_mem_nhds.2 (fun z hz ↦ ?_)
    filter_upwards [h z] with t ht
    exact h'.trans x z t hz ht.1
  have C : u.Nonempty := ⟨x, (mem_of_mem_nhds (h x)).1⟩
  have D : u = Set.univ := IsClopen.eq_univ ⟨A, B⟩ C
  change y ∈ u
  simp [D]

lemma PreconnectedSpace.induction₂ [PreconnectedSpace α] (P : α → α → Prop)
    (h : ∀ x, ∀ᶠ y in 𝓝 x, P x y) (h' : IsTrans α P) (h'' : Symmetric P) (x y : α) :
    P x y := by
  refine PreconnectedSpace.induction₂' P (fun z ↦ ?_) h' x y
  filter_upwards [h z] with a ha
  exact ⟨ha, h'' ha⟩

lemma IsPreconnected.induction₂ {s : Set α} (hs : IsPreconnected s) (P : α → α → Prop)
    (h : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, P x y)
    (h' : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → P x y → P y z → P x z)
    (h'' : ∀ x y, x ∈ s → y ∈ s → P x y → P y x)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : P x y := by
  apply hs.induction₂' P (fun z hz ↦ ?_) h' hx hy
  filter_upwards [h z hz, self_mem_nhdsWithin] with a ha h'a
  exact ⟨ha, h'' z a hz h'a ha⟩

theorem isPreconnected_iff_subset_of_disjoint {s : Set α} :
    IsPreconnected s ↔
      ∀ u v, IsOpen u → IsOpen v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

theorem isConnected_iff_sUnion_disjoint_open {s : Set α} :
    IsConnected s ↔
      ∀ U : Finset (Set α), (∀ u v : Set α, u ∈ U → v ∈ U → (s ∩ (u ∩ v)).Nonempty → u = v) →
        (∀ u ∈ U, IsOpen u) → (s ⊆ ⋃₀ ↑U) → ∃ u ∈ U, s ⊆ u := by
  rw [IsConnected, isPreconnected_iff_subset_of_disjoint]
  classical
  refine ⟨fun ⟨hne, h⟩ U hU hUo hsU => ?_, fun h => ⟨?_, fun u v hu hv hs hsuv => ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => exact absurd (by simpa using hsU) hne.not_subset_empty
    | insert u U uU IH =>
      simp only [← forall_cond_comm, Finset.forall_mem_insert, Finset.exists_mem_insert,
        Finset.coe_insert, sUnion_insert, implies_true, true_and] at *
      refine (h _ hUo.1 (⋃₀ ↑U) (isOpen_sUnion hUo.2) hsU ?_).imp_right ?_
      · refine subset_empty_iff.1 fun x ⟨hxs, hxu, v, hvU, hxv⟩ => ?_
        exact ne_of_mem_of_not_mem hvU uU (hU.1 v hvU ⟨x, hxs, hxu, hxv⟩).symm
      · exact IH (fun u hu => (hU.2 u hu).2) hUo.2
  · simpa [subset_empty_iff, nonempty_iff_ne_empty] using h ∅
  · rw [← not_nonempty_iff_eq_empty] at hsuv
    have := hsuv; rw [inter_comm u] at this
    simpa [*, or_imp, forall_and] using h {u, v}

theorem disjoint_or_subset_of_isClopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t) :
    Disjoint s t ∨ s ⊆ t :=
  (disjoint_or_nonempty_inter s t).imp_right <| hs.subset_isClopen ht

theorem isPreconnected_iff_subset_of_disjoint_closed :
    IsPreconnected s ↔
      ∀ u v, IsClosed u → IsClosed v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    rw [isPreconnected_closed_iff] at h
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · rw [isPreconnected_closed_iff]
    intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

theorem isPreconnected_iff_subset_of_fully_disjoint_closed {s : Set α} (hs : IsClosed s) :
    IsPreconnected s ↔
      ∀ u v, IsClosed u → IsClosed v → s ⊆ u ∪ v → Disjoint u v → s ⊆ u ∨ s ⊆ v := by
  refine isPreconnected_iff_subset_of_disjoint_closed.trans ⟨?_, ?_⟩ <;> intro H u v hu hv hss huv
  · apply H u v hu hv hss
    rw [huv.inter_eq, inter_empty]
  have H1 := H (u ∩ s) (v ∩ s)
  rw [subset_inter_iff, subset_inter_iff] at H1
  simp only [Subset.refl, and_true] at H1
  apply H1 (hu.inter hs) (hv.inter hs)
  · rw [← union_inter_distrib_right]
    exact subset_inter hss Subset.rfl
  · rwa [disjoint_iff_inter_eq_empty, ← inter_inter_distrib_right, inter_comm]

lemma IsClopen.isPreconnected_iff {s : Set α} (hs : IsClopen s) :
    IsPreconnected s ↔
      ∀ a b, IsClopen a → IsClopen b → a.Nonempty → b.Nonempty → Disjoint a b → s ≠ a ∪ b := by
  refine ⟨?_, fun H a b ha hb hsab hsa hsb ↦ ?_⟩
  · contrapose!
    rintro ⟨a, b, ha, hb, ha', hb', hab, rfl⟩ H
    exact (H a b ha.isOpen hb.isOpen subset_rfl (by rwa [union_inter_cancel_left])
      (by rwa [union_inter_cancel_right])).ne_empty (by grind)
  · rw [nonempty_iff_ne_empty]
    intro h
    exact H (s ∩ a) (s ∩ b)
      (isClopen_inter_of_disjoint_cover_clopen' hs hsab ha hb (by grind))
      (isClopen_inter_of_disjoint_cover_clopen' hs (by grind) hb ha (by grind))
      hsa hsb (by grind [Set.disjoint_iff_inter_eq_empty]) (by grind)

lemma IsClopen.not_isPreconnected_iff {s : Set α} (hs : IsClopen s) :
    ¬ IsPreconnected s ↔
      ∃ a b, IsClopen a ∧ IsClopen b ∧ a.Nonempty ∧ b.Nonempty ∧ Disjoint a b ∧ s = a ∪ b := by
  simp [hs.isPreconnected_iff]

theorem IsClopen.connectedComponent_subset {x} (hs : IsClopen s) (hx : x ∈ s) :
    connectedComponent x ⊆ s :=
  isPreconnected_connectedComponent.subset_isClopen hs ⟨x, mem_connectedComponent, hx⟩

theorem connectedComponent_subset_iInter_isClopen {x : α} :
    connectedComponent x ⊆ ⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z :=
  subset_iInter fun Z => Z.2.1.connectedComponent_subset Z.2.2

theorem IsClopen.biUnion_connectedComponent_eq {Z : Set α} (h : IsClopen Z) :
    ⋃ x ∈ Z, connectedComponent x = Z :=
  Subset.antisymm (iUnion₂_subset fun _ => h.connectedComponent_subset) fun _ h =>
    mem_iUnion₂_of_mem h mem_connectedComponent

open Set.Notation in

lemma IsClopen.biUnion_connectedComponentIn {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hu : IsClopen (v ↓∩ u)) (huv₁ : u ⊆ v) :
    u = ⋃ x ∈ u, connectedComponentIn v x := by
  have := congr(((↑) : Set v → Set X) $(hu.biUnion_connectedComponent_eq.symm))
  simp only [Subtype.image_preimage_coe, mem_preimage, iUnion_coe_set, image_val_iUnion,
    inter_eq_right.mpr huv₁] at this
  nth_rw 1 [this]
  congr! 2 with x hx
  simp only [← connectedComponentIn_eq_image]
  exact le_antisymm (iUnion_subset fun _ ↦ le_rfl) <|
    iUnion_subset fun hx ↦ subset_iUnion₂_of_subset (huv₁ hx) hx le_rfl

lemma IsClopen.connectedComponentIn_eq {U : Set α} (hU : IsClopen U) {x : α} (hx : x ∈ U) :
    connectedComponentIn U x = connectedComponent x :=
  subset_antisymm ((isPreconnected_connectedComponentIn).subset_connectedComponent
    (mem_connectedComponentIn hx)) <|
    (isPreconnected_connectedComponent).subset_connectedComponentIn (mem_connectedComponent)
    (hU.connectedComponent_subset hx)

variable [TopologicalSpace β] {f : α → β}

theorem Topology.IsCoinducing.isConnected_preimage_of_isClosed
    (connected_fibers : ∀ t : β, IsConnected (f ⁻¹' {t}))
    (hcl : IsCoinducing f) {t : Set β} (ht : IsClosed t) (ht' : IsConnected t) :
    IsConnected (f ⁻¹' t) := by
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : Surjective f := Surjective.of_comp fun t : β => (connected_fibers t).1
  refine ⟨Nonempty.preimage ht'.nonempty hf, ?_⟩
  have hT : IsClosed (f ⁻¹' t) :=
    hcl.isClosed_preimage.mpr ht
  -- To show it's preconnected we decompose (f ⁻¹' t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv uv_disj
  -- To do this we decompose t into T₁ and T₂
  -- we will show that t is a subset of either and hence
  -- (f ⁻¹' t) is a subset of u or v
  let T₁ := { t' ∈ t | f ⁻¹' {t'} ⊆ u }
  let T₂ := { t' ∈ t | f ⁻¹' {t'} ⊆ v }
  have fiber_decomp : ∀ t' ∈ t, f ⁻¹' {t'} ⊆ u ∨ f ⁻¹' {t'} ⊆ v := by
    intro t' ht'
    apply isPreconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv
    · exact Subset.trans (preimage_mono (singleton_subset_iff.2 ht')) huv
    rw [uv_disj.inter_eq, inter_empty]
  have T₁_u : f ⁻¹' T₁ = f ⁻¹' t ∩ u := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hau⟩
    constructor
    · exact mem_preimage.1 hat
    refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_right fun h => ?_
    exact uv_disj.subset_compl_right hau (h rfl)
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = f ⁻¹' t ∩ v := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hav⟩
    constructor
    · exact mem_preimage.1 hat
    · refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_left fun h => ?_
      exact uv_disj.subset_compl_left hav (h rfl)
  -- Now we show T₁, T₂ are closed, cover t and are disjoint.
  have hT₁ : IsClosed T₁ := hcl.isClosed_preimage.mp (T₁_u.symm ▸ IsClosed.inter hT hu)
  have hT₂ : IsClosed T₂ := hcl.isClosed_preimage.mp (T₂_v.symm ▸ IsClosed.inter hT hv)
  have T_decomp : t ⊆ T₁ ∪ T₂ := fun t' ht' => by
    rw [mem_union t' T₁ T₂]
    rcases fiber_decomp t' ht' with htu | htv
    · left; exact ⟨ht', htu⟩
    · right; exact ⟨ht', htv⟩
  have T_disjoint : Disjoint T₁ T₂ := by
    refine Disjoint.of_preimage hf ?_
    rw [T₁_u, T₂_v, disjoint_iff_inter_eq_empty, ← inter_inter_distrib_left, uv_disj.inter_eq,
      inter_empty]
  -- Now we do cases on whether t is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed ht).1
    ht'.isPreconnected T₁ T₂ hT₁ hT₂ T_decomp T_disjoint with h | h
  · left
    rw [Subset.antisymm_iff] at T₁_u
    suffices f ⁻¹' t ⊆ f ⁻¹' T₁
      from (this.trans T₁_u.1).trans inter_subset_right
    exact preimage_mono h
  · right
    rw [Subset.antisymm_iff] at T₂_v
    suffices f ⁻¹' t ⊆ f ⁻¹' T₂
      from (this.trans T₂_v.1).trans inter_subset_right
    exact preimage_mono h
