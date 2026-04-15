/-
Extracted from Topology/Compactness/Compact.lean
Genuine: 140 of 157 | Dissolved: 0 | Infrastructure: 17
-/
import Origin.Core
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Bases
import Mathlib.Data.Set.Accumulate
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Ultrafilter
import Mathlib.Topology.Defs.Ultrafilter

/-!
# Compact sets and compact spaces

## Main definitions

We define the following properties for sets in a topological space:

* `IsCompact`: a set such that each open cover has a finite subcover. This is defined in mathlib
  using filters. The main property of a compact set is `IsCompact.elim_finite_subcover`.
* `CompactSpace`: typeclass stating that the whole space is a compact set.
* `NoncompactSpace`: a space that is not a compact space.

## Main results

* `isCompact_univ_pi`: **Tychonov's theorem** - an arbitrary product of compact sets
  is compact.
-/

open Set Filter Topology TopologicalSpace Function

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X} {f : X → Y}

section Compact

lemma IsCompact.exists_clusterPt (hs : IsCompact s) {f : Filter X} [NeBot f] (hf : f ≤ 𝓟 s) :
    ∃ x ∈ s, ClusterPt x f := hs hf

lemma IsCompact.exists_mapClusterPt {ι : Type*} (hs : IsCompact s) {f : Filter ι} [NeBot f]
    {u : ι → X} (hf : Filter.map u f ≤ 𝓟 s) :
    ∃ x ∈ s, MapClusterPt x f u := hs hf

theorem IsCompact.compl_mem_sets (hs : IsCompact s) {f : Filter X} (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) :
    sᶜ ∈ f := by
  contrapose! hf
  simp only [not_mem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact @hs _ hf inf_le_right

theorem IsCompact.compl_mem_sets_of_nhdsWithin (hs : IsCompact s) {f : Filter X}
    (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine hs.compl_mem_sets fun x hx => ?_
  rcases hf x hx with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  rintro x ⟨h₁, h₂⟩ hs
  exact h₂ (h₁ hs)

@[elab_as_elim]
theorem IsCompact.induction_on (hs : IsCompact s) {p : Set X → Prop} (he : p ∅)
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s) (hunion : ∀ ⦃s t⦄, p s → p t → p (s ∪ t))
    (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter X := comk p he (fun _t ht _s hsub ↦ hmono hsub ht) (fun _s hs _t ht ↦ hunion hs ht)
  have : sᶜ ∈ f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using hnhds)
  rwa [← compl_compl s]

theorem IsCompact.inter_right (hs : IsCompact s) (ht : IsClosed t) : IsCompact (s ∩ t) := by
  intro f hnf hstf
  obtain ⟨x, hsx, hx⟩ : ∃ x ∈ s, ClusterPt x f :=
    hs (le_trans hstf (le_principal_iff.2 inter_subset_left))
  have : x ∈ t := ht.mem_of_nhdsWithin_neBot <|
    hx.mono <| le_trans hstf (le_principal_iff.2 inter_subset_right)
  exact ⟨x, ⟨hsx, this⟩, hx⟩

theorem IsCompact.inter_left (ht : IsCompact t) (hs : IsClosed s) : IsCompact (s ∩ t) :=
  inter_comm t s ▸ ht.inter_right hs

theorem IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCompact (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)

theorem IsCompact.of_isClosed_subset (hs : IsCompact s) (ht : IsClosed t) (h : t ⊆ s) :
    IsCompact t :=
  inter_eq_self_of_subset_right h ▸ hs.inter_right ht

theorem IsCompact.image_of_continuousOn {f : X → Y} (hs : IsCompact s) (hf : ContinuousOn f s) :
    IsCompact (f '' s) := by
  intro l lne ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this inf_le_right
  haveI := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

theorem IsCompact.image {f : X → Y} (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn

theorem IsCompact.adherence_nhdset {f : Filter X} (hs : IsCompact s) (hf₂ : f ≤ 𝓟 s)
    (ht₁ : IsOpen t) (ht₂ : ∀ x ∈ s, ClusterPt x f → x ∈ t) : t ∈ f :=
  Classical.by_cases mem_of_eq_bot fun (this : f ⊓ 𝓟 tᶜ ≠ ⊥) =>
    let ⟨x, hx, (hfx : ClusterPt x <| f ⊓ 𝓟 tᶜ)⟩ := @hs _ ⟨this⟩ <| inf_le_of_left_le hf₂
    have : x ∈ t := ht₂ x hx hfx.of_inf_left
    have : tᶜ ∩ t ∈ 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (IsOpen.mem_nhds ht₁ this)
    have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 <| compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x ≠ ⊥ := hfx.of_inf_right.ne
    absurd A this

theorem isCompact_iff_ultrafilter_le_nhds :
    IsCompact s ↔ ∀ f : Ultrafilter X, ↑f ≤ 𝓟 s → ∃ x ∈ s, ↑f ≤ 𝓝 x := by
  refine (forall_neBot_le_iff ?_).trans ?_
  · rintro f g hle ⟨x, hxs, hxf⟩
    exact ⟨x, hxs, hxf.mono hle⟩
  · simp only [Ultrafilter.clusterPt_iff]

alias ⟨IsCompact.ultrafilter_le_nhds, _⟩ := isCompact_iff_ultrafilter_le_nhds

theorem isCompact_iff_ultrafilter_le_nhds' :
    IsCompact s ↔ ∀ f : Ultrafilter X, s ∈ f → ∃ x ∈ s, ↑f ≤ 𝓝 x := by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff, Ultrafilter.mem_coe]

alias ⟨IsCompact.ultrafilter_le_nhds', _⟩ := isCompact_iff_ultrafilter_le_nhds'

lemma IsCompact.le_nhds_of_unique_clusterPt (hs : IsCompact s) {l : Filter X} {y : X}
    (hmem : s ∈ l) (h : ∀ x ∈ s, ClusterPt x l → x = y) : l ≤ 𝓝 y := by
  refine le_iff_ultrafilter.2 fun f hf ↦ ?_
  rcases hs.ultrafilter_le_nhds' f (hf hmem) with ⟨x, hxs, hx⟩
  convert ← hx
  exact h x hxs (.mono (.of_le_nhds hx) hf)

lemma IsCompact.tendsto_nhds_of_unique_mapClusterPt {Y} {l : Filter Y} {y : X} {f : Y → X}
    (hs : IsCompact s) (hmem : ∀ᶠ x in l, f x ∈ s) (h : ∀ x ∈ s, MapClusterPt x l f → x = y) :
    Tendsto f l (𝓝 y) :=
  hs.le_nhds_of_unique_clusterPt (mem_map.2 hmem) h

theorem IsCompact.elim_directed_cover {ι : Type v} [hι : Nonempty ι] (hs : IsCompact s)
    (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) (hdU : Directed (· ⊆ ·) U) :
    ∃ i, s ⊆ U i :=
  hι.elim fun i₀ =>
    IsCompact.induction_on hs ⟨i₀, empty_subset _⟩ (fun _ _ hs ⟨i, hi⟩ => ⟨i, hs.trans hi⟩)
      (fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ =>
        let ⟨k, hki, hkj⟩ := hdU i j
        ⟨k, union_subset (Subset.trans hi hki) (Subset.trans hj hkj)⟩)
      fun _x hx =>
      let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
      ⟨U i, mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (hUo i) hi), i, Subset.refl _⟩

theorem IsCompact.elim_finite_subcover {ι : Type v} (hs : IsCompact s) (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hsU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)

lemma IsCompact.elim_nhds_subcover_nhdsSet' (hs : IsCompact s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x hx, U x hx ∈ 𝓝 x) : ∃ t : Finset s, (⋃ x ∈ t, U x.1 x.2) ∈ 𝓝ˢ s := by
  rcases hs.elim_finite_subcover (fun x : s ↦ interior (U x x.2)) (fun _ ↦ isOpen_interior)
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 <| hU _ _⟩ with ⟨t, hst⟩
  refine ⟨t, mem_nhdsSet_iff_forall.2 fun x hx ↦ ?_⟩
  rcases mem_iUnion₂.1 (hst hx) with ⟨y, hyt, hy⟩
  refine mem_of_superset ?_ (subset_biUnion_of_mem hyt)
  exact mem_interior_iff_mem_nhds.1 hy

lemma IsCompact.elim_nhds_subcover_nhdsSet (hs : IsCompact s) {U : X → Set X}
    (hU : ∀ x ∈ s, U x ∈ 𝓝 x) : ∃ t : Finset X, (∀ x ∈ t, x ∈ s) ∧ (⋃ x ∈ t, U x) ∈ 𝓝ˢ s := by
  let ⟨t, ht⟩ := hs.elim_nhds_subcover_nhdsSet' (fun x _ => U x) hU
  classical
  exact ⟨t.image (↑), fun x hx =>
    let ⟨y, _, hyx⟩ := Finset.mem_image.1 hx
    hyx ▸ y.2,
    by rwa [Finset.set_biUnion_finset_image]⟩

theorem IsCompact.elim_nhds_subcover' (hs : IsCompact s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x (hx : x ∈ s), U x ‹x ∈ s› ∈ 𝓝 x) : ∃ t : Finset s, s ⊆ ⋃ x ∈ t, U (x : s) x.2 :=
  (hs.elim_nhds_subcover_nhdsSet' U hU).imp fun _ ↦ subset_of_mem_nhdsSet

theorem IsCompact.elim_nhds_subcover (hs : IsCompact s) (U : X → Set X) (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ t : Finset X, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x :=
  (hs.elim_nhds_subcover_nhdsSet hU).imp fun _ h ↦ h.imp_right subset_of_mem_nhdsSet

theorem IsCompact.disjoint_nhdsSet_left {l : Filter X} (hs : IsCompact s) :
    Disjoint (𝓝ˢ s) l ↔ ∀ x ∈ s, Disjoint (𝓝 x) l := by
  refine ⟨fun h x hx => h.mono_left <| nhds_le_nhdsSet hx, fun H => ?_⟩
  choose! U hxU hUl using fun x hx => (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx => (hUo x hx).mem_nhds (hxU x hx) with ⟨t, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x ∈ t, U x, ⟨isOpen_biUnion fun x hx => hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂, biInter_finset_mem]
  exact fun x hx => hUl x (hts x hx)

theorem IsCompact.disjoint_nhdsSet_right {l : Filter X} (hs : IsCompact s) :
    Disjoint l (𝓝ˢ s) ↔ ∀ x ∈ s, Disjoint l (𝓝 x) := by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

theorem IsCompact.elim_directed_family_closed {ι : Type v} [Nonempty ι] (hs : IsCompact s)
    (t : ι → Set X) (htc : ∀ i, IsClosed (t i)) (hst : (s ∩ ⋂ i, t i) = ∅)
    (hdt : Directed (· ⊇ ·) t) : ∃ i : ι, s ∩ t i = ∅ :=
  let ⟨t, ht⟩ :=
    hs.elim_directed_cover (compl ∘ t) (fun i => (htc i).isOpen_compl)
      (by
        simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_iUnion, exists_prop,
          mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using hst)
      (hdt.mono_comp _ fun _ _ => compl_subset_compl.mpr)
  ⟨t, by
    simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_iUnion, exists_prop,
      mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using ht⟩

theorem IsCompact.elim_finite_subfamily_closed {ι : Type v} (hs : IsCompact s)
    (t : ι → Set X) (htc : ∀ i, IsClosed (t i)) (hst : (s ∩ ⋂ i, t i) = ∅) :
    ∃ u : Finset ι, (s ∩ ⋂ i ∈ u, t i) = ∅ :=
  hs.elim_directed_family_closed _ (fun _ ↦ isClosed_biInter fun _ _ ↦ htc _)
    (by rwa [← iInter_eq_iInter_finset])
    (directed_of_isDirected_le fun _ _ h ↦ biInter_subset_biInter_left h)

theorem LocallyFinite.finite_nonempty_inter_compact {f : ι → Set X}
    (hf : LocallyFinite f) (hs : IsCompact s) : { i | (f i ∩ s).Nonempty }.Finite := by
  choose U hxU hUf using hf
  rcases hs.elim_nhds_subcover U fun x _ => hxU x with ⟨t, -, hsU⟩
  refine (t.finite_toSet.biUnion fun x _ => hUf x).subset ?_
  rintro i ⟨x, hx⟩
  rcases mem_iUnion₂.1 (hsU hx.2) with ⟨c, hct, hcx⟩
  exact mem_biUnion hct ⟨x, hx.1, hcx⟩

theorem IsCompact.inter_iInter_nonempty {ι : Type v} (hs : IsCompact s) (t : ι → Set X)
    (htc : ∀ i, IsClosed (t i)) (hst : ∀ u : Finset ι, (s ∩ ⋂ i ∈ u, t i).Nonempty) :
    (s ∩ ⋂ i, t i).Nonempty := by
  contrapose! hst
  exact hs.elim_finite_subfamily_closed t htc hst

theorem IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    {ι : Type v} [hι : Nonempty ι] (t : ι → Set X) (htd : Directed (· ⊇ ·) t)
    (htn : ∀ i, (t i).Nonempty) (htc : ∀ i, IsCompact (t i)) (htcl : ∀ i, IsClosed (t i)) :
    (⋂ i, t i).Nonempty := by
  let i₀ := hι.some
  suffices (t i₀ ∩ ⋂ i, t i).Nonempty by
    rwa [inter_eq_right.mpr (iInter_subset _ i₀)] at this
  simp only [nonempty_iff_ne_empty] at htn ⊢
  apply mt ((htc i₀).elim_directed_family_closed t htcl)
  push_neg
  simp only [← nonempty_iff_ne_empty] at htn ⊢
  refine ⟨htd, fun i => ?_⟩
  rcases htd i₀ i with ⟨j, hji₀, hji⟩
  exact (htn j).mono (subset_inter hji₀ hji)

alias IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed :=
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed

theorem IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    {S : Set (Set X)} [hS : Nonempty S] (hSd : DirectedOn (· ⊇ ·) S) (hSn : ∀ U ∈ S, U.Nonempty)
    (hSc : ∀ U ∈ S, IsCompact U) (hScl : ∀ U ∈ S, IsClosed U) : (⋂₀ S).Nonempty := by
  rw [sInter_eq_iInter]
  exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
    (DirectedOn.directed_val hSd) (fun i ↦ hSn i i.2) (fun i ↦ hSc i i.2) (fun i ↦ hScl i i.2)

theorem IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (t : ℕ → Set X)
    (htd : ∀ i, t (i + 1) ⊆ t i) (htn : ∀ i, (t i).Nonempty) (ht0 : IsCompact (t 0))
    (htcl : ∀ i, IsClosed (t i)) : (⋂ i, t i).Nonempty :=
  have tmono : Antitone t := antitone_nat_of_succ_le htd
  have htd : Directed (· ⊇ ·) t := tmono.directed_ge
  have : ∀ i, t i ⊆ t 0 := fun i => tmono <| Nat.zero_le i
  have htc : ∀ i, IsCompact (t i) := fun i => ht0.of_isClosed_subset (htcl i) (this i)
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl

alias IsCompact.nonempty_iInter_of_sequence_nonempty_compact_closed :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed

theorem IsCompact.elim_finite_subcover_image {b : Set ι} {c : ι → Set X} (hs : IsCompact s)
    (hc₁ : ∀ i ∈ b, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b', b' ⊆ b ∧ Set.Finite b' ∧ s ⊆ ⋃ i ∈ b', c i := by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_finite_subcover (fun i => c i : b → Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' d.toSet, ?_, d.finite_toSet.image _, ?_⟩
  · simp
  · rwa [biUnion_image]

theorem isCompact_of_finite_subcover
    (h : ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) →
      ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i) :
    IsCompact s := fun f hf hfs => by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose U hU hUf using h
  refine ⟨s, U, fun x => (hU x).2, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1⟩, fun t ht => ?_⟩
  refine compl_not_mem (le_principal_iff.1 hfs) ?_
  refine mem_of_superset ((biInter_finset_mem t).2 fun x _ => hUf x) ?_
  rw [subset_compl_comm, compl_iInter₂]
  simpa only [compl_compl]

theorem isCompact_of_finite_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ →
      ∃ u : Finset ι, (s ∩ ⋂ i ∈ u, t i) = ∅) :
    IsCompact s :=
  isCompact_of_finite_subcover fun U hUo hsU => by
    rw [← disjoint_compl_right_iff_subset, compl_iUnion, disjoint_iff] at hsU
    rcases h (fun i => (U i)ᶜ) (fun i => (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]

theorem isCompact_iff_finite_subcover :
    IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩

theorem isCompact_iff_finite_subfamily_closed :
    IsCompact s ↔ ∀ {ι : Type u} (t : ι → Set X),
      (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ → ∃ u : Finset ι, (s ∩ ⋂ i ∈ u, t i) = ∅ :=
  ⟨fun hs => hs.elim_finite_subfamily_closed, isCompact_of_finite_subfamily_closed⟩

theorem IsCompact.mem_nhdsSet_prod_of_forall {K : Set X} {Y} {l : Filter Y} {s : Set (X × Y)}
    (hK : IsCompact K) (hs : ∀ x ∈ K, s ∈ 𝓝 x ×ˢ l) : s ∈ (𝓝ˢ K) ×ˢ l := by
  refine hK.induction_on (by simp) (fun t t' ht hs ↦ ?_) (fun t t' ht ht' ↦ ?_) fun x hx ↦ ?_
  · exact prod_mono (nhdsSet_mono ht) le_rfl hs
  · simp [sup_prod, *]
  · rcases ((nhds_basis_opens _).prod l.basis_sets).mem_iff.1 (hs x hx)
      with ⟨⟨u, v⟩, ⟨⟨hx, huo⟩, hv⟩, hs⟩
    refine ⟨u, nhdsWithin_le_nhds (huo.mem_nhds hx), mem_of_superset ?_ hs⟩
    exact prod_mem_prod (huo.mem_nhdsSet.2 Subset.rfl) hv

theorem IsCompact.nhdsSet_prod_eq_biSup {K : Set X} (hK : IsCompact K) {Y} (l : Filter Y) :
    (𝓝ˢ K) ×ˢ l = ⨆ x ∈ K, 𝓝 x ×ˢ l :=
  le_antisymm (fun s hs ↦ hK.mem_nhdsSet_prod_of_forall <| by simpa using hs)
    (iSup₂_le fun _ hx ↦ prod_mono (nhds_le_nhdsSet hx) le_rfl)

theorem IsCompact.prod_nhdsSet_eq_biSup {K : Set Y} (hK : IsCompact K) {X} (l : Filter X) :
    l ×ˢ (𝓝ˢ K) = ⨆ y ∈ K, l ×ˢ 𝓝 y := by
  simp only [prod_comm (f := l), hK.nhdsSet_prod_eq_biSup, map_iSup]

theorem IsCompact.mem_prod_nhdsSet_of_forall {K : Set Y} {X} {l : Filter X} {s : Set (X × Y)}
    (hK : IsCompact K) (hs : ∀ y ∈ K, s ∈ l ×ˢ 𝓝 y) : s ∈ l ×ˢ 𝓝ˢ K :=
  (hK.prod_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

theorem IsCompact.nhdsSet_inf_eq_biSup {K : Set X} (hK : IsCompact K) (l : Filter X) :
    (𝓝ˢ K) ⊓ l = ⨆ x ∈ K, 𝓝 x ⊓ l := by
  have : ∀ f : Filter X, f ⊓ l = comap (fun x ↦ (x, x)) (f ×ˢ l) := fun f ↦ by
    simpa only [comap_prod] using congrArg₂ (· ⊓ ·) comap_id.symm comap_id.symm
  simp_rw [this, ← comap_iSup, hK.nhdsSet_prod_eq_biSup]

theorem IsCompact.inf_nhdsSet_eq_biSup {K : Set X} (hK : IsCompact K) (l : Filter X) :
    l ⊓ (𝓝ˢ K) = ⨆ x ∈ K, l ⊓ 𝓝 x := by
  simp only [inf_comm l, hK.nhdsSet_inf_eq_biSup]

theorem IsCompact.mem_nhdsSet_inf_of_forall {K : Set X} {l : Filter X} {s : Set X}
    (hK : IsCompact K) (hs : ∀ x ∈ K, s ∈ 𝓝 x ⊓ l) : s ∈ (𝓝ˢ K) ⊓ l :=
  (hK.nhdsSet_inf_eq_biSup l).symm ▸ by simpa using hs

theorem IsCompact.mem_inf_nhdsSet_of_forall {K : Set X} {l : Filter X} {s : Set X}
    (hK : IsCompact K) (hs : ∀ y ∈ K, s ∈ l ⊓ 𝓝 y) : s ∈ l ⊓ 𝓝ˢ K :=
  (hK.inf_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

theorem IsCompact.eventually_forall_of_forall_eventually {x₀ : X} {K : Set Y} (hK : IsCompact K)
    {P : X → Y → Prop} (hP : ∀ y ∈ K, ∀ᶠ z : X × Y in 𝓝 (x₀, y), P z.1 z.2) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, P x y := by
  simp only [nhds_prod_eq, ← eventually_iSup, ← hK.prod_nhdsSet_eq_biSup] at hP
  exact hP.curry.mono fun _ h ↦ h.self_of_nhdsSet

@[simp]
theorem isCompact_empty : IsCompact (∅ : Set X) := fun _f hnf hsf =>
  Not.elim hnf.ne <| empty_mem_iff_bot.1 <| le_principal_iff.1 hsf

@[simp]
theorem isCompact_singleton {x : X} : IsCompact ({x} : Set X) := fun _ hf hfa =>
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩

theorem Set.Subsingleton.isCompact (hs : s.Subsingleton) : IsCompact s :=
  Subsingleton.induction_on hs isCompact_empty fun _ => isCompact_singleton

theorem Set.Finite.isCompact_biUnion {s : Set ι} {f : ι → Set X} (hs : s.Finite)
    (hf : ∀ i ∈ s, IsCompact (f i)) : IsCompact (⋃ i ∈ s, f i) :=
  isCompact_iff_ultrafilter_le_nhds'.2 fun l hl => by
    rw [Ultrafilter.finite_biUnion_mem_iff hs] at hl
    rcases hl with ⟨i, his, hi⟩
    rcases (hf i his).ultrafilter_le_nhds _ (le_principal_iff.2 hi) with ⟨x, hxi, hlx⟩
    exact ⟨x, mem_iUnion₂.2 ⟨i, his, hxi⟩, hlx⟩

theorem Finset.isCompact_biUnion (s : Finset ι) {f : ι → Set X} (hf : ∀ i ∈ s, IsCompact (f i)) :
    IsCompact (⋃ i ∈ s, f i) :=
  s.finite_toSet.isCompact_biUnion hf

theorem isCompact_accumulate {K : ℕ → Set X} (hK : ∀ n, IsCompact (K n)) (n : ℕ) :
    IsCompact (Accumulate K n) :=
  (finite_le_nat n).isCompact_biUnion fun k _ => hK k

theorem Set.Finite.isCompact_sUnion {S : Set (Set X)} (hf : S.Finite) (hc : ∀ s ∈ S, IsCompact s) :
    IsCompact (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isCompact_biUnion hc

theorem isCompact_iUnion {ι : Sort*} {f : ι → Set X} [Finite ι] (h : ∀ i, IsCompact (f i)) :
    IsCompact (⋃ i, f i) :=
  (finite_range f).isCompact_sUnion <| forall_mem_range.2 h

theorem Set.Finite.isCompact (hs : s.Finite) : IsCompact s :=
  biUnion_of_singleton s ▸ hs.isCompact_biUnion fun _ _ => isCompact_singleton

theorem IsCompact.finite_of_discrete [DiscreteTopology X] (hs : IsCompact s) : s.Finite := by
  have : ∀ x : X, ({x} : Set X) ∈ 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, _, hst⟩
  simp only [← t.set_biUnion_coe, biUnion_of_singleton] at hst
  exact t.finite_toSet.subset hst

theorem isCompact_iff_finite [DiscreteTopology X] : IsCompact s ↔ s.Finite :=
  ⟨fun h => h.finite_of_discrete, fun h => h.isCompact⟩

theorem IsCompact.union (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∪ t) := by
  rw [union_eq_iUnion]; exact isCompact_iUnion fun b => by cases b <;> assumption

protected theorem IsCompact.insert (hs : IsCompact s) (a) : IsCompact (insert a s) :=
  isCompact_singleton.union hs

theorem exists_subset_nhds_of_isCompact' [Nonempty ι] {V : ι → Set X}
    (hV : Directed (· ⊇ ·) V) (hV_cpct : ∀ i, IsCompact (V i)) (hV_closed : ∀ i, IsClosed (V i))
    {U : Set X} (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U := by
  obtain ⟨W, hsubW, W_op, hWU⟩ := exists_open_set_nhds hU
  suffices ∃ i, V i ⊆ W from this.imp fun i hi => hi.trans hWU
  by_contra! H
  replace H : ∀ i, (V i ∩ Wᶜ).Nonempty := fun i => Set.inter_compl_nonempty_iff.mpr (H i)
  have : (⋂ i, V i ∩ Wᶜ).Nonempty := by
    refine
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun i j => ?_) H
        (fun i => (hV_cpct i).inter_right W_op.isClosed_compl) fun i =>
        (hV_closed i).inter W_op.isClosed_compl
    rcases hV i j with ⟨k, hki, hkj⟩
    refine ⟨k, ⟨fun x => ?_, fun x => ?_⟩⟩ <;> simp only [and_imp, mem_inter_iff, mem_compl_iff] <;>
      tauto
  have : ¬⋂ i : ι, V i ⊆ W := by simpa [← iInter_inter, inter_compl_nonempty_iff]
  contradiction

lemma eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open (b : ι → Set X)
    (hb : IsTopologicalBasis (Set.range b)) (U : Set X) (hUc : IsCompact U) (hUo : IsOpen U) :
    ∃ s : Set ι, s.Finite ∧ U = ⋃ i ∈ s, b i := by
  obtain ⟨Y, f, e, hf⟩ := hb.open_eq_iUnion hUo
  choose f' hf' using hf
  have : b ∘ f' = f := funext hf'
  subst this
  obtain ⟨t, ht⟩ :=
    hUc.elim_finite_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) (by rw [e])
  classical
  refine ⟨t.image f', Set.toFinite _, le_antisymm ?_ ?_⟩
  · refine Set.Subset.trans ht ?_
    simp only [Set.iUnion_subset_iff]
    intro i hi
    erw [← Set.iUnion_subtype (fun x : ι => x ∈ t.image f') fun i => b i.1]
    exact Set.subset_iUnion (fun i : t.image f' => b i) ⟨_, Finset.mem_image_of_mem _ hi⟩
  · apply Set.iUnion₂_subset
    rintro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    rw [e]
    exact Set.subset_iUnion (b ∘ f') j

lemma eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open (b : Set (Set X))
    (hb : IsTopologicalBasis b) (U : Set X) (hUc : IsCompact U) (hUo : IsOpen U) :
    ∃ s : Finset b, U = s.toSet.sUnion := by
  have hb' : b = range (fun i ↦ i : b → Set X) := by simp
  rw [hb'] at hb
  choose s hs hU using eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U hUc hUo
  have : Finite s := hs
  let _ : Fintype s := Fintype.ofFinite _
  use s.toFinset
  simp [hU]

theorem isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis (b : ι → Set X)
    (hb : IsTopologicalBasis (Set.range b)) (hb' : ∀ i, IsCompact (b i)) (U : Set X) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set ι, s.Finite ∧ U = ⋃ i ∈ s, b i := by
  constructor
  · exact fun ⟨h₁, h₂⟩ ↦ eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U h₁ h₂
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact hs.isCompact_biUnion fun i _ => hb' i
    · exact isOpen_biUnion fun i _ => hb.isOpen (Set.mem_range_self _)

namespace Filter

theorem hasBasis_cocompact : (cocompact X).HasBasis IsCompact compl :=
  hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s ∪ t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isCompact_empty⟩

theorem mem_cocompact : s ∈ cocompact X ↔ ∃ t, IsCompact t ∧ tᶜ ⊆ s :=
  hasBasis_cocompact.mem_iff

theorem mem_cocompact' : s ∈ cocompact X ↔ ∃ t, IsCompact t ∧ sᶜ ⊆ t :=
  mem_cocompact.trans <| exists_congr fun _ => and_congr_right fun _ => compl_subset_comm

theorem _root_.IsCompact.compl_mem_cocompact (hs : IsCompact s) : sᶜ ∈ Filter.cocompact X :=
  hasBasis_cocompact.mem_of_mem hs

theorem cocompact_le_cofinite : cocompact X ≤ cofinite := fun s hs =>
  compl_compl s ▸ hs.isCompact.compl_mem_cocompact

theorem cocompact_eq_cofinite (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    cocompact X = cofinite := by
  simp only [cocompact, hasBasis_cofinite.eq_biInf, isCompact_iff_finite]

theorem disjoint_cocompact_left (f : Filter X) :
    Disjoint (Filter.cocompact X) f ↔ ∃ K ∈ f, IsCompact K := by
  simp_rw [hasBasis_cocompact.disjoint_iff_left, compl_compl]
  tauto

theorem disjoint_cocompact_right (f : Filter X) :
    Disjoint f (Filter.cocompact X) ↔ ∃ K ∈ f, IsCompact K := by
  simp_rw [hasBasis_cocompact.disjoint_iff_right, compl_compl]
  tauto

theorem _root_.Nat.cocompact_eq : cocompact ℕ = atTop :=
  (cocompact_eq_cofinite ℕ).trans Nat.cofinite_eq_atTop

theorem Tendsto.isCompact_insert_range_of_cocompact {f : X → Y} {y}
    (hf : Tendsto f (cocompact X) (𝓝 y)) (hfc : Continuous f) : IsCompact (insert y (range f)) := by
  intro l hne hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_cocompact.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K ∈ l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsy, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
  exact ⟨y, Or.inr <| image_subset_range _ _ hy, hyl⟩

theorem Tendsto.isCompact_insert_range_of_cofinite {f : ι → X} {x} (hf : Tendsto f cofinite (𝓝 x)) :
    IsCompact (insert x (range f)) := by
  letI : TopologicalSpace ι := ⊥; haveI h : DiscreteTopology ι := ⟨rfl⟩
  rw [← cocompact_eq_cofinite ι] at hf
  exact hf.isCompact_insert_range_of_cocompact continuous_of_discreteTopology

theorem Tendsto.isCompact_insert_range {f : ℕ → X} {x} (hf : Tendsto f atTop (𝓝 x)) :
    IsCompact (insert x (range f)) :=
  Filter.Tendsto.isCompact_insert_range_of_cofinite <| Nat.cofinite_eq_atTop.symm ▸ hf

theorem hasBasis_coclosedCompact :
    (Filter.coclosedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl := by
  simp only [Filter.coclosedCompact, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isCompact_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s ∪ t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩⟩

theorem mem_coclosedCompact_iff :
    s ∈ coclosedCompact X ↔ IsCompact (closure sᶜ) := by
  refine hasBasis_coclosedCompact.mem_iff.trans ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨t, ⟨htcl, htco⟩, hst⟩
    exact htco.of_isClosed_subset isClosed_closure <|
      closure_minimal (compl_subset_comm.2 hst) htcl
  · exact ⟨closure sᶜ, ⟨isClosed_closure, h⟩, compl_subset_comm.2 subset_closure⟩

theorem mem_coclosedCompact : s ∈ coclosedCompact X ↔ ∃ t, IsClosed t ∧ IsCompact t ∧ tᶜ ⊆ s := by
  simp only [hasBasis_coclosedCompact.mem_iff, and_assoc]

theorem mem_coclosed_compact' : s ∈ coclosedCompact X ↔ ∃ t, IsClosed t ∧ IsCompact t ∧ sᶜ ⊆ t := by
  simp only [hasBasis_coclosedCompact.mem_iff, compl_subset_comm, and_assoc]

theorem compl_mem_coclosedCompact : sᶜ ∈ coclosedCompact X ↔ IsCompact (closure s) := by
  rw [mem_coclosedCompact_iff, compl_compl]

theorem cocompact_le_coclosedCompact : cocompact X ≤ coclosedCompact X :=
  iInf_mono fun _ => le_iInf fun _ => le_rfl

end Filter

theorem IsCompact.compl_mem_coclosedCompact_of_isClosed (hs : IsCompact s) (hs' : IsClosed s) :
    sᶜ ∈ Filter.coclosedCompact X :=
  hasBasis_coclosedCompact.mem_of_mem ⟨hs', hs⟩

namespace Bornology

variable (X) in

def inCompact : Bornology X where
  cobounded' := Filter.cocompact X
  le_cofinite' := Filter.cocompact_le_cofinite

theorem inCompact.isBounded_iff : @IsBounded _ (inCompact X) s ↔ ∃ t, IsCompact t ∧ s ⊆ t := by
  change sᶜ ∈ Filter.cocompact X ↔ _
  rw [Filter.mem_cocompact]
  simp

end Bornology

theorem IsCompact.nhdsSet_prod_eq {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t := by
  simp_rw [hs.nhdsSet_prod_eq_biSup, ht.prod_nhdsSet_eq_biSup, nhdsSet, sSup_image, biSup_prod,
    nhds_prod_eq]

theorem nhdsSet_prod_le_of_disjoint_cocompact {f : Filter Y} (hs : IsCompact s)
    (hf : Disjoint f (Filter.cocompact Y)) :
    𝓝ˢ s ×ˢ f ≤ 𝓝ˢ (s ×ˢ Set.univ) := by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    𝓝ˢ s ×ˢ f
    _ ≤ 𝓝ˢ s ×ˢ 𝓟 K        := Filter.prod_mono_right _ (Filter.le_principal_iff.mpr hKf)
    _ ≤ 𝓝ˢ s ×ˢ 𝓝ˢ K       := Filter.prod_mono_right _ principal_le_nhdsSet
    _ = 𝓝ˢ (s ×ˢ K)         := (hs.nhdsSet_prod_eq hK).symm
    _ ≤ 𝓝ˢ (s ×ˢ Set.univ)  := nhdsSet_mono (prod_mono_right le_top)

theorem prod_nhdsSet_le_of_disjoint_cocompact {f : Filter X} (ht : IsCompact t)
    (hf : Disjoint f (Filter.cocompact X)) :
    f ×ˢ 𝓝ˢ t ≤ 𝓝ˢ (Set.univ ×ˢ t) := by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    f ×ˢ 𝓝ˢ t
    _ ≤ (𝓟 K) ×ˢ 𝓝ˢ t      := Filter.prod_mono_left _ (Filter.le_principal_iff.mpr hKf)
    _ ≤ 𝓝ˢ K ×ˢ 𝓝ˢ t       := Filter.prod_mono_left _ principal_le_nhdsSet
    _ = 𝓝ˢ (K ×ˢ t)         := (hK.nhdsSet_prod_eq ht).symm
    _ ≤ 𝓝ˢ (Set.univ ×ˢ t)  := nhdsSet_mono (prod_mono_left le_top)

theorem generalized_tube_lemma (hs : IsCompact s) {t : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : IsOpen n) (hp : s ×ˢ t ⊆ n) :
    ∃ (u : Set X) (v : Set Y), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n := by
  rw [← hn.mem_nhdsSet, hs.nhdsSet_prod_eq ht,
    ((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).mem_iff] at hp
  rcases hp with ⟨⟨u, v⟩, ⟨⟨huo, hsu⟩, hvo, htv⟩, hn⟩
  exact ⟨u, v, huo, hvo, hsu, htv, hn⟩

instance (priority := 10) Subsingleton.compactSpace [Subsingleton X] : CompactSpace X :=
  ⟨subsingleton_univ.isCompact⟩

theorem isCompact_univ_iff : IsCompact (univ : Set X) ↔ CompactSpace X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

theorem isCompact_univ [h : CompactSpace X] : IsCompact (univ : Set X) :=
  h.isCompact_univ

theorem exists_clusterPt_of_compactSpace [CompactSpace X] (f : Filter X) [NeBot f] :
    ∃ x, ClusterPt x f := by
  simpa using isCompact_univ (show f ≤ 𝓟 univ by simp)

nonrec theorem Ultrafilter.le_nhds_lim [CompactSpace X] (F : Ultrafilter X) : ↑F ≤ 𝓝 F.lim := by
  rcases isCompact_univ.ultrafilter_le_nhds F (by simp) with ⟨x, -, h⟩
  exact le_nhds_lim ⟨x, h⟩

theorem CompactSpace.elim_nhds_subcover [CompactSpace X] (U : X → Set X) (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset X, ⋃ x ∈ t, U x = ⊤ := by
  obtain ⟨t, -, s⟩ := IsCompact.elim_nhds_subcover isCompact_univ U fun x _ => hU x
  exact ⟨t, top_unique s⟩

theorem compactSpace_of_finite_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → ⋂ i, t i = ∅ →
      ∃ u : Finset ι, ⋂ i ∈ u, t i = ∅) :
    CompactSpace X where
  isCompact_univ := isCompact_of_finite_subfamily_closed fun t => by simpa using h t

theorem IsClosed.isCompact [CompactSpace X] (h : IsClosed s) : IsCompact s :=
  isCompact_univ.of_isClosed_subset h (subset_univ _)

lemma le_nhds_of_unique_clusterPt [CompactSpace X] {l : Filter X} {y : X}
    (h : ∀ x, ClusterPt x l → x = y) : l ≤ 𝓝 y :=
  isCompact_univ.le_nhds_of_unique_clusterPt univ_mem fun x _ ↦ h x

lemma tendsto_nhds_of_unique_mapClusterPt [CompactSpace X] {Y} {l : Filter Y} {y : X} {f : Y → X}
    (h : ∀ x, MapClusterPt x l f → x = y) :
    Tendsto f l (𝓝 y) :=
  le_nhds_of_unique_clusterPt h

lemma noncompact_univ (X : Type*) [TopologicalSpace X] [NoncompactSpace X] :
    ¬IsCompact (univ : Set X) :=
  NoncompactSpace.noncompact_univ

theorem IsCompact.ne_univ [NoncompactSpace X] (hs : IsCompact s) : s ≠ univ := fun h =>
  noncompact_univ X (h ▸ hs)

instance [NoncompactSpace X] : NeBot (Filter.cocompact X) := by
  refine Filter.hasBasis_cocompact.neBot_iff.2 fun hs => ?_
  contrapose hs; rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]; exact noncompact_univ X

@[simp]
theorem Filter.cocompact_eq_bot [CompactSpace X] : Filter.cocompact X = ⊥ :=
  Filter.hasBasis_cocompact.eq_bot_iff.mpr ⟨Set.univ, isCompact_univ, Set.compl_univ⟩

instance [NoncompactSpace X] : NeBot (Filter.coclosedCompact X) :=
  neBot_of_le Filter.cocompact_le_coclosedCompact

theorem noncompactSpace_of_neBot (_ : NeBot (Filter.cocompact X)) : NoncompactSpace X :=
  ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_cocompact).ne_empty compl_univ⟩

theorem Filter.cocompact_neBot_iff : NeBot (Filter.cocompact X) ↔ NoncompactSpace X :=
  ⟨noncompactSpace_of_neBot, fun _ => inferInstance⟩

theorem not_compactSpace_iff : ¬CompactSpace X ↔ NoncompactSpace X :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩

instance : NoncompactSpace ℤ :=
  noncompactSpace_of_neBot <| by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

theorem finite_of_compact_of_discrete [CompactSpace X] [DiscreteTopology X] : Finite X :=
  Finite.of_finite_univ <| isCompact_univ.finite_of_discrete

lemma Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact
    {K : Set X} (hs : s.Infinite) (hK : IsCompact K) (hsub : s ⊆ K) :
    ∃ x ∈ K, AccPt x (cofinite ⊓ 𝓟 s) :=
  (@hK _ hs.cofinite_inf_principal_neBot (inf_le_right.trans <| principal_mono.2 hsub)).imp
    fun x hx ↦ by rwa [acc_iff_cluster, inf_comm, inf_right_comm,
      (finite_singleton _).cofinite_inf_principal_compl]

lemma Set.Infinite.exists_accPt_of_subset_isCompact {K : Set X} (hs : s.Infinite)
    (hK : IsCompact K) (hsub : s ⊆ K) : ∃ x ∈ K, AccPt x (𝓟 s) :=
  let ⟨x, hxK, hx⟩ := hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact hK hsub
  ⟨x, hxK, hx.mono inf_le_right⟩

lemma Set.Infinite.exists_accPt_cofinite_inf_principal [CompactSpace X] (hs : s.Infinite) :
    ∃ x, AccPt x (cofinite ⊓ 𝓟 s) := by
  simpa only [mem_univ, true_and]
    using hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact isCompact_univ s.subset_univ

lemma Set.Infinite.exists_accPt_principal [CompactSpace X] (hs : s.Infinite) : ∃ x, AccPt x (𝓟 s) :=
  hs.exists_accPt_cofinite_inf_principal.imp fun _x hx ↦ hx.mono inf_le_right

theorem exists_nhds_ne_neBot (X : Type*) [TopologicalSpace X] [CompactSpace X] [Infinite X] :
    ∃ z : X, (𝓝[≠] z).NeBot := by
  simpa [AccPt] using (@infinite_univ X _).exists_accPt_principal

theorem finite_cover_nhds_interior [CompactSpace X] {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset X, ⋃ x ∈ t, interior (U x) = univ :=
  let ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, univ_subset_iff.1 ht⟩

theorem finite_cover_nhds [CompactSpace X] {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset X, ⋃ x ∈ t, U x = univ :=
  let ⟨t, ht⟩ := finite_cover_nhds_interior hU
  ⟨t, univ_subset_iff.1 <| ht.symm.subset.trans <| iUnion₂_mono fun _ _ => interior_subset⟩

theorem LocallyFinite.finite_nonempty_of_compact [CompactSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) : { i | (f i).Nonempty }.Finite := by
  simpa only [inter_univ] using hf.finite_nonempty_inter_compact isCompact_univ

theorem LocallyFinite.finite_of_compact [CompactSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : (univ : Set ι).Finite := by
  simpa only [hne] using hf.finite_nonempty_of_compact

noncomputable def LocallyFinite.fintypeOfCompact [CompactSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : Fintype ι :=
  fintypeOfFiniteUniv (hf.finite_of_compact hne)

theorem Filter.comap_cocompact_le {f : X → Y} (hf : Continuous f) :
    (Filter.cocompact Y).comap f ≤ Filter.cocompact X := by
  rw [(Filter.hasBasis_cocompact.comap f).le_basis_iff Filter.hasBasis_cocompact]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

theorem isCompact_range [CompactSpace X] {f : X → Y} (hf : Continuous f) : IsCompact (range f) := by
  rw [← image_univ]; exact isCompact_univ.image hf

theorem isCompact_diagonal [CompactSpace X] : IsCompact (diagonal X) :=
  @range_diag X ▸ isCompact_range (continuous_id.prod_mk continuous_id)

theorem isClosedMap_snd_of_compactSpace [CompactSpace X] :
    IsClosedMap (Prod.snd : X × Y → Y) := fun s hs => by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  have : univ ×ˢ {y} ⊆ sᶜ := by
    exact fun (x, y') ⟨_, rfl⟩ hs => hy ⟨(x, y'), hs, rfl⟩
  rcases generalized_tube_lemma isCompact_univ isCompact_singleton hs.isOpen_compl this
    with ⟨U, V, -, hVo, hU, hV, hs⟩
  refine mem_nhds_iff.2 ⟨V, ?_, hVo, hV rfl⟩
  rintro _ hzV ⟨z, hzs, rfl⟩
  exact hs ⟨hU trivial, hzV⟩ hzs

theorem isClosedMap_fst_of_compactSpace [CompactSpace Y] : IsClosedMap (Prod.fst : X × Y → X) :=
  isClosedMap_snd_of_compactSpace.comp isClosedMap_swap

theorem exists_subset_nhds_of_compactSpace [CompactSpace X] [Nonempty ι]
    {V : ι → Set X} (hV : Directed (· ⊇ ·) V) (hV_closed : ∀ i, IsClosed (V i)) {U : Set X}
    (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
  exists_subset_nhds_of_isCompact' hV (fun i => (hV_closed i).isCompact) hV_closed hU

theorem Topology.IsInducing.isCompact_iff {f : X → Y} (hf : IsInducing f) :
    IsCompact s ↔ IsCompact (f '' s) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x ∈ s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

theorem Topology.IsEmbedding.isCompact_iff {f : X → Y} (hf : IsEmbedding f) :
    IsCompact s ↔ IsCompact (f '' s) := hf.isInducing.isCompact_iff

alias Embedding.isCompact_iff := IsEmbedding.isCompact_iff

theorem Topology.IsInducing.isCompact_preimage (hf : IsInducing f) (hf' : IsClosed (range f))
    {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [hf.isCompact_iff, image_preimage_eq_inter_range]

alias Inducing.isCompact_preimage := IsInducing.isCompact_preimage

lemma Topology.IsInducing.isCompact_preimage_iff {f : X → Y} (hf : IsInducing f) {K : Set Y}
    (Kf : K ⊆ range f) : IsCompact (f ⁻¹' K) ↔ IsCompact K := by
  rw [hf.isCompact_iff, image_preimage_eq_of_subset Kf]

alias Inducing.isCompact_preimage_iff := IsInducing.isCompact_preimage_iff

lemma Topology.IsInducing.isCompact_preimage' (hf : IsInducing f) {K : Set Y}
    (hK : IsCompact K) (Kf : K ⊆ range f) : IsCompact (f ⁻¹' K) :=
  (hf.isCompact_preimage_iff Kf).2 hK

alias Inducing.isCompact_preimage' := IsInducing.isCompact_preimage'

theorem Topology.IsClosedEmbedding.isCompact_preimage (hf : IsClosedEmbedding f)
    {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K) :=
  hf.isInducing.isCompact_preimage (hf.isClosed_range) hK

alias ClosedEmbedding.isCompact_preimage := IsClosedEmbedding.isCompact_preimage

theorem Topology.IsClosedEmbedding.tendsto_cocompact (hf : IsClosedEmbedding f) :
    Tendsto f (Filter.cocompact X) (Filter.cocompact Y) :=
  Filter.hasBasis_cocompact.tendsto_right_iff.mpr fun _K hK =>
    (hf.isCompact_preimage hK).compl_mem_cocompact

alias ClosedEmbedding.tendsto_cocompact := IsClosedEmbedding.tendsto_cocompact

theorem Subtype.isCompact_iff {p : X → Prop} {s : Set { x // p x }} :
    IsCompact s ↔ IsCompact ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isCompact_iff

theorem isCompact_iff_isCompact_univ : IsCompact s ↔ IsCompact (univ : Set s) := by
  rw [Subtype.isCompact_iff, image_univ, Subtype.range_coe]

theorem isCompact_iff_compactSpace : IsCompact s ↔ CompactSpace s :=
  isCompact_iff_isCompact_univ.trans isCompact_univ_iff

theorem IsCompact.finite (hs : IsCompact s) (hs' : DiscreteTopology s) : s.Finite :=
  finite_coe_iff.mp (@finite_of_compact_of_discrete _ _ (isCompact_iff_compactSpace.mp hs) hs')

theorem exists_nhds_ne_inf_principal_neBot (hs : IsCompact s) (hs' : s.Infinite) :
    ∃ z ∈ s, (𝓝[≠] z ⊓ 𝓟 s).NeBot :=
  hs'.exists_accPt_of_subset_isCompact hs Subset.rfl

protected theorem Topology.IsClosedEmbedding.noncompactSpace [NoncompactSpace X] {f : X → Y}
    (hf : IsClosedEmbedding f) : NoncompactSpace Y :=
  noncompactSpace_of_neBot hf.tendsto_cocompact.neBot

alias ClosedEmbedding.noncompactSpace := IsClosedEmbedding.noncompactSpace

protected theorem Topology.IsClosedEmbedding.compactSpace [h : CompactSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) : CompactSpace X :=
  ⟨by rw [hf.isInducing.isCompact_iff, image_univ]; exact hf.isClosed_range.isCompact⟩

alias ClosedEmbedding.compactSpace := IsClosedEmbedding.compactSpace

theorem IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ˢ t) := by
  rw [isCompact_iff_ultrafilter_le_nhds'] at hs ht ⊢
  intro f hfs
  obtain ⟨x : X, sx : x ∈ s, hx : map Prod.fst f.1 ≤ 𝓝 x⟩ :=
    hs (f.map Prod.fst) (mem_map.2 <| mem_of_superset hfs fun x => And.left)
  obtain ⟨y : Y, ty : y ∈ t, hy : map Prod.snd f.1 ≤ 𝓝 y⟩ :=
    ht (f.map Prod.snd) (mem_map.2 <| mem_of_superset hfs fun x => And.right)
  rw [map_le_iff_le_comap] at hx hy
  refine ⟨⟨x, y⟩, ⟨sx, ty⟩, ?_⟩
  rw [nhds_prod_eq]; exact le_inf hx hy

instance (priority := 100) Finite.compactSpace [Finite X] : CompactSpace X where
  isCompact_univ := finite_univ.isCompact

instance ULift.compactSpace [CompactSpace X] : CompactSpace (ULift.{v} X) :=
  IsClosedEmbedding.uliftDown.compactSpace

instance [CompactSpace X] [CompactSpace Y] : CompactSpace (X × Y) :=
  ⟨by rw [← univ_prod_univ]; exact isCompact_univ.prod isCompact_univ⟩

instance [CompactSpace X] [CompactSpace Y] : CompactSpace (X ⊕ Y) :=
  ⟨by
    rw [← range_inl_union_range_inr]
    exact (isCompact_range continuous_inl).union (isCompact_range continuous_inr)⟩

instance {X : ι → Type*} [Finite ι] [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] :
    CompactSpace (Σi, X i) := by
  refine ⟨?_⟩
  rw [Sigma.univ]
  exact isCompact_iUnion fun i => isCompact_range continuous_sigmaMk

theorem Filter.coprod_cocompact :
    (Filter.cocompact X).coprod (Filter.cocompact Y) = Filter.cocompact (X × Y) := by
  apply le_antisymm
  · exact sup_le (comap_cocompact_le continuous_fst) (comap_cocompact_le continuous_snd)
  · refine (hasBasis_cocompact.coprod hasBasis_cocompact).ge_iff.2 fun K hK ↦ ?_
    rw [← univ_prod, ← prod_univ, ← compl_prod_eq_union]
    exact (hK.1.prod hK.2).compl_mem_cocompact

theorem Prod.noncompactSpace_iff :
    NoncompactSpace (X × Y) ↔ NoncompactSpace X ∧ Nonempty Y ∨ Nonempty X ∧ NoncompactSpace Y := by
  simp [← Filter.cocompact_neBot_iff, ← Filter.coprod_cocompact, Filter.coprod_neBot_iff]

instance (priority := 100) Prod.noncompactSpace_left [NoncompactSpace X] [Nonempty Y] :
    NoncompactSpace (X × Y) :=
  Prod.noncompactSpace_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

instance (priority := 100) Prod.noncompactSpace_right [Nonempty X] [NoncompactSpace Y] :
    NoncompactSpace (X × Y) :=
  Prod.noncompactSpace_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

section Tychonoff

variable {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

theorem isCompact_pi_infinite {s : ∀ i, Set (X i)} :
    (∀ i, IsCompact (s i)) → IsCompact { x : ∀ i, X i | ∀ i, x i ∈ s i } := by
  simp only [isCompact_iff_ultrafilter_le_nhds, nhds_pi, le_pi, le_principal_iff]
  intro h f hfs
  have : ∀ i : ι, ∃ x, x ∈ s i ∧ Tendsto (Function.eval i) f (𝓝 x) := by
    refine fun i => h i (f.map _) (mem_map.2 ?_)
    exact mem_of_superset hfs fun x hx => hx i
  choose x hx using this
  exact ⟨x, fun i => (hx i).left, fun i => (hx i).right⟩

theorem isCompact_univ_pi {s : ∀ i, Set (X i)} (h : ∀ i, IsCompact (s i)) :
    IsCompact (pi univ s) := by
  convert isCompact_pi_infinite h
  simp only [← mem_univ_pi, setOf_mem_eq]

instance Pi.compactSpace [∀ i, CompactSpace (X i)] : CompactSpace (∀ i, X i) :=
  ⟨by rw [← pi_univ univ]; exact isCompact_univ_pi fun i => isCompact_univ⟩

instance Function.compactSpace [CompactSpace Y] : CompactSpace (ι → Y) :=
  Pi.compactSpace

lemma Pi.isCompact_iff_of_isClosed {s : Set (Π i, X i)} (hs : IsClosed s) :
    IsCompact s ↔ ∀ i, IsCompact (eval i '' s) := by
  constructor <;> intro H
  · exact fun i ↦ H.image <| continuous_apply i
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H) hs (subset_pi_eval_image univ s)

protected lemma Pi.exists_compact_superset_iff {s : Set (Π i, X i)} :
    (∃ K, IsCompact K ∧ s ⊆ K) ↔ ∀ i, ∃ Ki, IsCompact Ki ∧ s ⊆ eval i ⁻¹' Ki := by
  constructor
  · intro ⟨K, hK, hsK⟩ i
    exact ⟨eval i '' K, hK.image <| continuous_apply i, hsK.trans <| K.subset_preimage_image _⟩
  · intro H
    choose K hK hsK using H
    exact ⟨pi univ K, isCompact_univ_pi hK, fun _ hx i _ ↦ hsK i hx⟩

theorem Filter.coprodᵢ_cocompact {X : ι → Type*} [∀ d, TopologicalSpace (X d)] :
    (Filter.coprodᵢ fun d => Filter.cocompact (X d)) = Filter.cocompact (∀ d, X d) := by
  refine le_antisymm (iSup_le fun i => Filter.comap_cocompact_le (continuous_apply i)) ?_
  refine compl_surjective.forall.2 fun s H => ?_
  simp only [compl_mem_coprodᵢ, Filter.mem_cocompact, compl_subset_compl, image_subset_iff] at H ⊢
  choose K hKc htK using H
  exact ⟨Set.pi univ K, isCompact_univ_pi hKc, fun f hf i _ => htK i hf⟩

end Tychonoff

instance Quot.compactSpace {r : X → X → Prop} [CompactSpace X] : CompactSpace (Quot r) :=
  ⟨by
    rw [← range_quot_mk]
    exact isCompact_range continuous_quot_mk⟩

instance Quotient.compactSpace {s : Setoid X} [CompactSpace X] : CompactSpace (Quotient s) :=
  Quot.compactSpace

theorem IsClosed.exists_minimal_nonempty_closed_subset [CompactSpace X] {S : Set X}
    (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ V : Set X, V ⊆ S ∧ V.Nonempty ∧ IsClosed V ∧
      ∀ V' : Set X, V' ⊆ V → V'.Nonempty → IsClosed V' → V' = V := by
  let opens := { U : Set X | Sᶜ ⊆ U ∧ IsOpen U ∧ Uᶜ.Nonempty }
  obtain ⟨U, h⟩ :=
    zorn_subset opens fun c hc hz => by
      by_cases hcne : c.Nonempty
      · obtain ⟨U₀, hU₀⟩ := hcne
        haveI : Nonempty { U // U ∈ c } := ⟨⟨U₀, hU₀⟩⟩
        obtain ⟨U₀compl, -, -⟩ := hc hU₀
        use ⋃₀ c
        refine ⟨⟨?_, ?_, ?_⟩, fun U hU _ hx => ⟨U, hU, hx⟩⟩
        · exact fun _ hx => ⟨U₀, hU₀, U₀compl hx⟩
        · exact isOpen_sUnion fun _ h => (hc h).2.1
        · convert_to (⋂ U : { U // U ∈ c }, U.1ᶜ).Nonempty
          · ext
            simp only [not_exists, exists_prop, not_and, Set.mem_iInter, Subtype.forall,
              mem_setOf_eq, mem_compl_iff, mem_sUnion]
          apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          · rintro ⟨U, hU⟩ ⟨U', hU'⟩
            obtain ⟨V, hVc, hVU, hVU'⟩ := hz.directedOn U hU U' hU'
            exact ⟨⟨V, hVc⟩, Set.compl_subset_compl.mpr hVU, Set.compl_subset_compl.mpr hVU'⟩
          · exact fun U => (hc U.2).2.2
          · exact fun U => (hc U.2).2.1.isClosed_compl.isCompact
          · exact fun U => (hc U.2).2.1.isClosed_compl
      · use Sᶜ
        refine ⟨⟨Set.Subset.refl _, isOpen_compl_iff.mpr hS, ?_⟩, fun U Uc => (hcne ⟨U, Uc⟩).elim⟩
        rw [compl_compl]
        exact hne
  obtain ⟨Uc, Uo, Ucne⟩ := h.prop
  refine ⟨Uᶜ, Set.compl_subset_comm.mp Uc, Ucne, Uo.isClosed_compl, ?_⟩
  intro V' V'sub V'ne V'cls
  have : V'ᶜ = U := by
    refine h.eq_of_ge ⟨?_, isOpen_compl_iff.mpr V'cls, ?_⟩ (subset_compl_comm.2 V'sub)
    · exact Set.Subset.trans Uc (Set.subset_compl_comm.mp V'sub)
    · simp only [compl_compl, V'ne]
  rw [← this, compl_compl]

end Compact
