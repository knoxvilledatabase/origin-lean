/-
Extracted from Topology/UniformSpace/Compact.lean
Genuine: 10 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Compactness.Compact

noncomputable section

/-!
# Compact sets in uniform spaces

* `compactSpace_uniformity`: On a compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagonal.

-/

universe u v ua ub uc ud

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

section Compact

open Uniformity Set Filter UniformSpace

open scoped Topology

variable [UniformSpace α] {K : Set α}

theorem lebesgue_number_lemma {ι : Sort*} {U : ι → Set α} (hK : IsCompact K)
    (hopen : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ i, ball x V ⊆ U i := by
  have : ∀ x ∈ K, ∃ i, ∃ V ∈ 𝓤 α, ball x (V ○ V) ⊆ U i := fun x hx ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover hx)
    rw [← (hopen i).mem_nhds_iff, nhds_eq_comap_uniformity, ← lift'_comp_uniformity] at hi
    exact ⟨i, (((basis_sets _).lift' <| monotone_id.compRel monotone_id).comap _).mem_iff.1 hi⟩
  choose ind W hW hWU using this
  rcases hK.elim_nhds_subcover' (fun x hx ↦ ball x (W x hx)) (fun x hx ↦ ball_mem_nhds _ (hW x hx))
    with ⟨t, ht⟩
  refine ⟨⋂ x ∈ t, W x x.2, (biInter_finset_mem _).2 fun x _ ↦ hW x x.2, fun x hx ↦ ?_⟩
  rcases mem_iUnion₂.1 (ht hx) with ⟨y, hyt, hxy⟩
  exact ⟨ind y y.2, fun z hz ↦ hWU _ _ ⟨x, hxy, mem_iInter₂.1 hz _ hyt⟩⟩

protected theorem Filter.HasBasis.lebesgue_number_lemma {ι' ι : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : ι → Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hopen : ∀ j, IsOpen (U j)) (hcover : K ⊆ ⋃ j, U j) :
    ∃ i, p i ∧ ∀ x ∈ K, ∃ j, ball x (V i) ⊆ U j := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma hK hopen hcover)
  exact fun s t hst ht x hx ↦ (ht x hx).imp fun i hi ↦ Subset.trans (ball_mono hst _) hi

theorem lebesgue_number_lemma_sUnion {S : Set (Set α)}
    (hK : IsCompact K) (hopen : ∀ s ∈ S, IsOpen s) (hcover : K ⊆ ⋃₀ S) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ s ∈ S, ball x V ⊆ s := by
  rw [sUnion_eq_iUnion] at hcover
  simpa using lebesgue_number_lemma hK (by simpa) hcover

theorem IsCompact.nhdsSet_basis_uniformity {p : ι → Prop} {V : ι → Set (α × α)}
    (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis p fun i => ⋃ x ∈ K, ball x (V i) where
  mem_iff' U := by
    constructor
    · intro H
      have HKU : K ⊆ ⋃ _ : Unit, interior U := by
        simpa only [iUnion_const, subset_interior_iff_mem_nhdsSet] using H
      obtain ⟨i, hpi, hi⟩ : ∃ i, p i ∧ ⋃ x ∈ K, ball x (V i) ⊆ interior U := by
        simpa using hbasis.lebesgue_number_lemma hK (fun _ ↦ isOpen_interior) HKU
      exact ⟨i, hpi, hi.trans interior_subset⟩
    · rintro ⟨i, hpi, hi⟩
      refine mem_of_superset (bUnion_mem_nhdsSet fun x _ ↦ ?_) hi
      exact ball_mem_nhds _ <| hbasis.mem_of_mem hpi

theorem Disjoint.exists_uniform_thickening {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ V ∈ 𝓤 α, Disjoint (⋃ x ∈ A, ball x V) (⋃ x ∈ B, ball x V) := by
  have : Bᶜ ∈ 𝓝ˢ A := hB.isOpen_compl.mem_nhdsSet.mpr h.le_compl_right
  rw [(hA.nhdsSet_basis_uniformity (Filter.basis_sets _)).mem_iff] at this
  rcases this with ⟨U, hU, hUAB⟩
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
  refine ⟨V, hV, Set.disjoint_left.mpr fun x => ?_⟩
  simp only [mem_iUnion₂]
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
  rw [mem_ball_symmetry hVsymm] at hxa hxb
  exact hUAB (mem_iUnion₂_of_mem ha <| hVU <| mem_comp_of_mem_ball hVsymm hxa hxb) hb

theorem Disjoint.exists_uniform_thickening_of_basis {p : ι → Prop} {s : ι → Set (α × α)}
    (hU : (𝓤 α).HasBasis p s) {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ i, p i ∧ Disjoint (⋃ x ∈ A, ball x (s i)) (⋃ x ∈ B, ball x (s i)) := by
  rcases h.exists_uniform_thickening hA hB with ⟨V, hV, hVAB⟩
  rcases hU.mem_iff.1 hV with ⟨i, hi, hiV⟩
  exact ⟨i, hi, hVAB.mono (iUnion₂_mono fun a _ => ball_mono hiV a)
    (iUnion₂_mono fun b _ => ball_mono hiV b)⟩

theorem lebesgue_number_of_compact_open {K U : Set α} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) : ∃ V ∈ 𝓤 α, IsOpen V ∧ ∀ x ∈ K, UniformSpace.ball x V ⊆ U :=
  let ⟨V, ⟨hV, hVo⟩, hVU⟩ :=
    (hK.nhdsSet_basis_uniformity uniformity_hasBasis_open).mem_iff.1 (hU.mem_nhdsSet.2 hKU)
  ⟨V, hV, hVo, iUnion₂_subset_iff.1 hVU⟩

theorem nhdsSet_diagonal_eq_uniformity [CompactSpace α] : 𝓝ˢ (diagonal α) = 𝓤 α := by
  refine nhdsSet_diagonal_le_uniformity.antisymm ?_
  have :
    (𝓤 (α × α)).HasBasis (fun U => U ∈ 𝓤 α) fun U =>
      (fun p : (α × α) × α × α => ((p.1.1, p.2.1), p.1.2, p.2.2)) ⁻¹' U ×ˢ U := by
    rw [uniformity_prod_eq_comap_prod]
    exact (𝓤 α).basis_sets.prod_self.comap _
  refine (isCompact_diagonal.nhdsSet_basis_uniformity this).ge_iff.2 fun U hU => ?_
  exact mem_of_superset hU fun ⟨x, y⟩ hxy => mem_iUnion₂.2
    ⟨(x, x), rfl, refl_mem_uniformity hU, hxy⟩

theorem compactSpace_uniformity [CompactSpace α] : 𝓤 α = ⨆ x, 𝓝 (x, x) :=
  nhdsSet_diagonal_eq_uniformity.symm.trans (nhdsSet_diagonal _)

theorem unique_uniformity_of_compact [t : TopologicalSpace γ] [CompactSpace γ]
    {u u' : UniformSpace γ} (h : u.toTopologicalSpace = t) (h' : u'.toTopologicalSpace = t) :
    u = u' := by
  refine UniformSpace.ext ?_
  have : @CompactSpace γ u.toTopologicalSpace := by rwa [h]
  have : @CompactSpace γ u'.toTopologicalSpace := by rwa [h']
  rw [@compactSpace_uniformity _ u, compactSpace_uniformity, h, h']

end Compact
