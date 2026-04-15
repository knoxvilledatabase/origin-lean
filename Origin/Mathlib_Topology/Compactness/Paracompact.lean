/-
Extracted from Topology/Compactness/Paracompact.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.Topology.Homeomorph
import Mathlib.Data.Option.Basic

/-!
# Paracompact topological spaces

A topological space `X` is said to be paracompact if every open covering of `X` admits a locally
finite refinement.

The definition requires that each set of the new covering is a subset of one of the sets of the
initial covering. However, one can ensure that each open covering `s : ι → Set X` admits a *precise*
locally finite refinement, i.e., an open covering `t : ι → Set X` with the same index set such that
`∀ i, t i ⊆ s i`, see lemma `precise_refinement`. We also provide a convenience lemma
`precise_refinement_set` that deals with open coverings of a closed subset of `X` instead of the
whole space.

We also prove the following facts.

* Every compact space is paracompact, see instance `paracompact_of_compact`.

* A locally compact sigma compact Hausdorff space is paracompact, see instance
  `paracompact_of_locallyCompact_sigmaCompact`. Moreover, we can choose a locally finite
  refinement with sets in a given collection of filter bases of `𝓝 x`, `x : X`, see
  `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis`. For example, in a proper metric space
  every open covering `⋃ i, s i` admits a refinement `⋃ i, Metric.ball (c i) (r i)`.

* Every paracompact Hausdorff space is normal. This statement is not an instance to avoid loops in
  the instance graph.

* Every `EMetricSpace` is a paracompact space, see instance `EMetric.instParacompactSpace` in
  `Topology/EMetricSpace/Paracompact`.

## TODO

Prove (some of) [Michael's theorems](https://ncatlab.org/nlab/show/Michael%27s+theorem).

## Tags

compact space, paracompact space, locally finite covering
-/

open Set Filter Function

open Filter Topology

universe u v w

class ParacompactSpace (X : Type v) [TopologicalSpace X] : Prop where
  /-- Every open cover of a paracompact space assumes a locally finite refinement. -/
  locallyFinite_refinement :
    ∀ (α : Type v) (s : α → Set X), (∀ a, IsOpen (s a)) → (⋃ a, s a = univ) →
      ∃ (β : Type v) (t : β → Set X),
        (∀ b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a

variable {ι : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

theorem precise_refinement [ParacompactSpace X] (u : ι → Set X) (uo : ∀ a, IsOpen (u a))
    (uc : ⋃ i, u i = univ) : ∃ v : ι → Set X, (∀ a, IsOpen (v a)) ∧ ⋃ i, v i = univ ∧
    LocallyFinite v ∧ ∀ a, v a ⊆ u a := by
  -- Apply definition to `range u`, then turn existence quantifiers into functions using `choose`
  have := ParacompactSpace.locallyFinite_refinement (range u) (fun r ↦ (r : Set X))
    (forall_subtype_range_iff.2 uo) (by rwa [← sUnion_range, Subtype.range_coe])
  simp only [exists_subtype_range_iff, iUnion_eq_univ_iff] at this
  choose α t hto hXt htf ind hind using this
  choose t_inv ht_inv using hXt
  choose U hxU hU using htf
  -- Send each `i` to the union of `t a` over `a ∈ ind ⁻¹' {i}`
  refine ⟨fun i ↦ ⋃ (a : α) (_ : ind a = i), t a, ?_, ?_, ?_, ?_⟩
  · exact fun a ↦ isOpen_iUnion fun a ↦ isOpen_iUnion fun _ ↦ hto a
  · simp only [eq_univ_iff_forall, mem_iUnion]
    exact fun x ↦ ⟨ind (t_inv x), _, rfl, ht_inv _⟩
  · refine fun x ↦ ⟨U x, hxU x, ((hU x).image ind).subset ?_⟩
    simp only [subset_def, mem_iUnion, mem_setOf_eq, Set.Nonempty, mem_inter_iff]
    rintro i ⟨y, ⟨a, rfl, hya⟩, hyU⟩
    exact mem_image_of_mem _ ⟨y, hya, hyU⟩
  · simp only [subset_def, mem_iUnion]
    rintro i x ⟨a, rfl, hxa⟩
    exact hind _ hxa

theorem precise_refinement_set [ParacompactSpace X] {s : Set X} (hs : IsClosed s) (u : ι → Set X)
    (uo : ∀ i, IsOpen (u i)) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, (∀ i, IsOpen (v i)) ∧ (s ⊆ ⋃ i, v i) ∧ LocallyFinite v ∧ ∀ i, v i ⊆ u i := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10888): added proof of uc
  have uc : (iUnion fun i => Option.elim' sᶜ u i) = univ := by
    apply Subset.antisymm (subset_univ _)
    · simp_rw [← compl_union_self s, Option.elim', iUnion_option]
      apply union_subset_union_right sᶜ us
  rcases precise_refinement (Option.elim' sᶜ u) (Option.forall.2 ⟨isOpen_compl_iff.2 hs, uo⟩)
      uc with
    ⟨v, vo, vc, vf, vu⟩
  refine ⟨v ∘ some, fun i ↦ vo _, ?_, vf.comp_injective (Option.some_injective _), fun i ↦ vu _⟩
  · simp only [iUnion_option, ← compl_subset_iff_union] at vc
    exact Subset.trans (subset_compl_comm.1 <| vu Option.none) vc

theorem Topology.IsClosedEmbedding.paracompactSpace [ParacompactSpace Y] {e : X → Y}
    (he : IsClosedEmbedding e) : ParacompactSpace X where
  locallyFinite_refinement α s ho hu := by
    choose U hUo hU using fun a ↦ he.isOpen_iff.1 (ho a)
    simp only [← hU] at hu ⊢
    have heU : range e ⊆ ⋃ i, U i := by
      simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using hu
    rcases precise_refinement_set he.isClosed_range U hUo heU with ⟨V, hVo, heV, hVf, hVU⟩
    refine ⟨α, fun a ↦ e ⁻¹' (V a), fun a ↦ (hVo a).preimage he.continuous, ?_,
      hVf.preimage_continuous he.continuous, fun a ↦ ⟨a, preimage_mono (hVU a)⟩⟩
    simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using heV

alias ClosedEmbedding.paracompactSpace := IsClosedEmbedding.paracompactSpace

theorem Homeomorph.paracompactSpace_iff (e : X ≃ₜ Y) : ParacompactSpace X ↔ ParacompactSpace Y :=
  ⟨fun _ ↦ e.symm.isClosedEmbedding.paracompactSpace, fun _ ↦ e.isClosedEmbedding.paracompactSpace⟩

instance (priority := 200) [CompactSpace X] [ParacompactSpace Y] : ParacompactSpace (X × Y) where
  locallyFinite_refinement α s ho hu := by
    have : ∀ (x : X) (y : Y), ∃ (a : α) (U : Set X) (V : Set Y),
        IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ×ˢ V ⊆ s a := fun x y ↦
      (iUnion_eq_univ_iff.1 hu (x, y)).imp fun a ha ↦ isOpen_prod_iff.1 (ho a) x y ha
    choose a U V hUo hVo hxU hyV hUV using this
    choose T hT using fun y ↦ CompactSpace.elim_nhds_subcover (U · y) fun x ↦
      (hUo x y).mem_nhds (hxU x y)
    set W : Y → Set Y := fun y ↦ ⋂ x ∈ T y, V x y
    have hWo : ∀ y, IsOpen (W y) := fun y ↦ isOpen_biInter_finset fun _ _ ↦ hVo _ _
    have hW : ∀ y, y ∈ W y := fun _ ↦ mem_iInter₂.2 fun _ _ ↦ hyV _ _
    rcases precise_refinement W hWo (iUnion_eq_univ_iff.2 fun y ↦ ⟨y, hW y⟩)
      with ⟨E, hEo, hE, hEf, hEA⟩
    refine ⟨Σ y, T y, fun z ↦ U z.2.1 z.1 ×ˢ E z.1, fun _ ↦ (hUo _ _).prod (hEo _),
      iUnion_eq_univ_iff.2 fun (x, y) ↦ ?_, fun (x, y) ↦ ?_, fun ⟨y, x, hx⟩ ↦ ?_⟩
    · rcases iUnion_eq_univ_iff.1 hE y with ⟨b, hb⟩
      rcases iUnion₂_eq_univ_iff.1 (hT b) x with ⟨a, ha, hx⟩
      exact ⟨⟨b, a, ha⟩, hx, hb⟩
    · rcases hEf y with ⟨t, ht, htf⟩
      refine ⟨univ ×ˢ t, prod_mem_nhds univ_mem ht, ?_⟩
      refine (htf.biUnion fun y _ ↦ finite_range (Sigma.mk y)).subset ?_
      rintro ⟨b, a, ha⟩ ⟨⟨c, d⟩, ⟨-, hd : d ∈ E b⟩, -, hdt : d ∈ t⟩
      exact mem_iUnion₂.2 ⟨b, ⟨d, hd, hdt⟩, mem_range_self _⟩
    · refine ⟨a x y, (Set.prod_mono Subset.rfl ?_).trans (hUV x y)⟩
      exact (hEA _).trans (iInter₂_subset x hx)

instance (priority := 200) [ParacompactSpace X] [CompactSpace Y] : ParacompactSpace (X × Y) :=
  (Homeomorph.prodComm X Y).paracompactSpace_iff.2 inferInstance

instance (priority := 100) paracompact_of_compact [CompactSpace X] : ParacompactSpace X := by
  -- the proof is trivial: we choose a finite subcover using compactness, and use it
  refine ⟨fun ι s ho hu ↦ ?_⟩
  rcases isCompact_univ.elim_finite_subcover _ ho hu.ge with ⟨T, hT⟩
  refine ⟨(T : Set ι), fun t ↦ s t, fun t ↦ ho _, ?_, locallyFinite_of_finite _,
    fun t ↦ ⟨t, Subset.rfl⟩⟩
  simpa only [iUnion_coe_set, ← univ_subset_iff]

theorem refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] {ι : X → Type u} {p : ∀ x, ι x → Prop} {B : ∀ x, ι x → Set X}
    {s : Set X} (hs : IsClosed s) (hB : ∀ x ∈ s, (𝓝 x).HasBasis (p x) (B x)) :
    ∃ (α : Type v) (c : α → X) (r : ∀ a, ι (c a)),
      (∀ a, c a ∈ s ∧ p (c a) (r a)) ∧
        (s ⊆ ⋃ a, B (c a) (r a)) ∧ LocallyFinite fun a ↦ B (c a) (r a) := by
  classical
    -- For technical reasons we prepend two empty sets to the sequence `CompactExhaustion.choice X`
    set K' : CompactExhaustion X := CompactExhaustion.choice X
    set K : CompactExhaustion X := K'.shiftr.shiftr
    set Kdiff := fun n ↦ K (n + 1) \ interior (K n)
    -- Now we restate some properties of `CompactExhaustion` for `K`/`Kdiff`
    have hKcov : ∀ x, x ∈ Kdiff (K'.find x + 1) := fun x ↦ by
      simpa only [K'.find_shiftr] using
        diff_subset_diff_right interior_subset (K'.shiftr.mem_diff_shiftr_find x)
    have Kdiffc : ∀ n, IsCompact (Kdiff n ∩ s) :=
      fun n ↦ ((K.isCompact _).diff isOpen_interior).inter_right hs
    -- Next we choose a finite covering `B (c n i) (r n i)` of each
    -- `Kdiff (n + 1) ∩ s` such that `B (c n i) (r n i) ∩ s` is disjoint with `K n`
    have : ∀ (n) (x : ↑(Kdiff (n + 1) ∩ s)), (K n)ᶜ ∈ 𝓝 (x : X) :=
      fun n x ↦ (K.isClosed n).compl_mem_nhds fun hx' ↦ x.2.1.2 <| K.subset_interior_succ _ hx'
    -- Porting note: Commented out `haveI` for now.
    --haveI : ∀ (n) (x : ↑(Kdiff n ∩ s)), Nonempty (ι x) := fun n x ↦ (hB x x.2.2).nonempty
    choose! r hrp hr using fun n (x : ↑(Kdiff (n + 1) ∩ s)) ↦ (hB x x.2.2).mem_iff.1 (this n x)
    have hxr : ∀ (n x) (hx : x ∈ Kdiff (n + 1) ∩ s), B x (r n ⟨x, hx⟩) ∈ 𝓝 x := fun n x hx ↦
      (hB x hx.2).mem_of_mem (hrp _ ⟨x, hx⟩)
    choose T hT using fun n ↦ (Kdiffc (n + 1)).elim_nhds_subcover' _ (hxr n)
    set T' : ∀ n, Set ↑(Kdiff (n + 1) ∩ s) := fun n ↦ T n
    -- Finally, we take the union of all these coverings
    refine ⟨Σn, T' n, fun a ↦ a.2, fun a ↦ r a.1 a.2, ?_, ?_, ?_⟩
    · rintro ⟨n, x, hx⟩
      exact ⟨x.2.2, hrp _ _⟩
    · refine fun x hx ↦ mem_iUnion.2 ?_
      rcases mem_iUnion₂.1 (hT _ ⟨hKcov x, hx⟩) with ⟨⟨c, hc⟩, hcT, hcx⟩
      exact ⟨⟨_, ⟨c, hc⟩, hcT⟩, hcx⟩
    · intro x
      refine
        ⟨interior (K (K'.find x + 3)),
          IsOpen.mem_nhds isOpen_interior (K.subset_interior_succ _ (hKcov x).1), ?_⟩
      have : (⋃ k ≤ K'.find x + 2, range (Sigma.mk k) : Set (Σn, T' n)).Finite :=
        (finite_le_nat _).biUnion fun k _ ↦ finite_range _
      apply this.subset
      rintro ⟨k, c, hc⟩
      simp only [mem_iUnion, mem_setOf_eq, mem_image, Subtype.coe_mk]
      rintro ⟨x, hxB : x ∈ B c (r k c), hxK⟩
      refine ⟨k, ?_, ⟨c, hc⟩, rfl⟩
      have := (mem_compl_iff _ _).1 (hr k c hxB)
      contrapose! this with hnk
      exact K.subset hnk (interior_subset hxK)

theorem refinement_of_locallyCompact_sigmaCompact_of_nhds_basis [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] {ι : X → Type u} {p : ∀ x, ι x → Prop} {B : ∀ x, ι x → Set X}
    (hB : ∀ x, (𝓝 x).HasBasis (p x) (B x)) :
    ∃ (α : Type v) (c : α → X) (r : ∀ a, ι (c a)),
      (∀ a, p (c a) (r a)) ∧ ⋃ a, B (c a) (r a) = univ ∧ LocallyFinite fun a ↦ B (c a) (r a) :=
  let ⟨α, c, r, hp, hU, hfin⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set isClosed_univ fun x _ ↦ hB x
  ⟨α, c, r, fun a ↦ (hp a).2, univ_subset_iff.1 hU, hfin⟩

instance (priority := 100) paracompact_of_locallyCompact_sigmaCompact [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] : ParacompactSpace X := by
  refine ⟨fun α s ho hc ↦ ?_⟩
  choose i hi using iUnion_eq_univ_iff.1 hc
  have : ∀ x : X, (𝓝 x).HasBasis (fun t : Set X ↦ (x ∈ t ∧ IsOpen t) ∧ t ⊆ s (i x)) id :=
    fun x : X ↦ (nhds_basis_opens x).restrict_subset (IsOpen.mem_nhds (ho (i x)) (hi x))
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis this with
    ⟨β, c, t, hto, htc, htf⟩
  exact ⟨β, t, fun x ↦ (hto x).1.2, htc, htf, fun b ↦ ⟨i <| c b, (hto b).2⟩⟩

instance (priority := 100) T4Space.of_paracompactSpace_t2Space [T2Space X] [ParacompactSpace X] :
    T4Space X := by
  -- First we show how to go from points to a set on one side.
  have : ∀ s t : Set X, IsClosed s →
      (∀ x ∈ s, ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ t ⊆ v ∧ Disjoint u v) →
      ∃ u v, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v := fun s t hs H ↦ by
    /- For each `x ∈ s` we choose open disjoint `u x ∋ x` and `v x ⊇ t`. The sets `u x` form an
        open covering of `s`. We choose a locally finite refinement `u' : s → Set X`, then
        `⋃ i, u' i` and `(closure (⋃ i, u' i))ᶜ` are disjoint open neighborhoods of `s` and `t`. -/
    choose u v hu hv hxu htv huv using SetCoe.forall'.1 H
    rcases precise_refinement_set hs u hu fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxu _⟩ with
      ⟨u', hu'o, hcov', hu'fin, hsub⟩
    refine ⟨⋃ i, u' i, (closure (⋃ i, u' i))ᶜ, isOpen_iUnion hu'o, isClosed_closure.isOpen_compl,
      hcov', ?_, disjoint_compl_right.mono le_rfl (compl_le_compl subset_closure)⟩
    rw [hu'fin.closure_iUnion, compl_iUnion, subset_iInter_iff]
    refine fun i x hxt hxu ↦
      absurd (htv i hxt) (closure_minimal ?_ (isClosed_compl_iff.2 <| hv _) hxu)
    exact fun y hyu hyv ↦ (huv i).le_bot ⟨hsub _ hyu, hyv⟩
  -- Now we apply the lemma twice: first to `s` and `t`, then to `t` and each point of `s`.
  refine { normal := fun s t hs ht hst ↦ this s t hs fun x hx ↦ ?_ }
  rcases this t {x} ht fun y hy ↦ (by
    simp_rw [singleton_subset_iff]
    exact t2_separation (hst.symm.ne_of_mem hy hx))
    with ⟨v, u, hv, hu, htv, hxu, huv⟩
  exact ⟨u, v, hu, hv, singleton_subset_iff.1 hxu, htv, huv.symm⟩
