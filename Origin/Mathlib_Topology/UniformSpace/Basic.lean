/-
Extracted from Topology/UniformSpace/Basic.lean
Genuine: 39 of 55 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core

/-!
# Basic results on uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups.

## Main definitions

In this file we define a complete lattice structure on the type `UniformSpace X`
of uniform structures on `X`, as well as the pullback (`UniformSpace.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notation

Localized in `Uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`,
and `○` for composition of relations, seen as terms with type `Set (X × X)`.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/

open Set Filter Topology

open scoped SetRel Uniformity

universe u v ua ub uc ud

/-!
### Relations, seen as `SetRel α α`
-/

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

open scoped SetRel in

lemma IsOpen.relComp [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {s : SetRel α β} {t : SetRel β γ} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ○ t) := by
  conv =>
    arg 1; equals ⋃ b, (fun p => (p.1, b)) ⁻¹' s ∩ (fun p => (b, p.2)) ⁻¹' t => ext ⟨_, _⟩; simp
  exact isOpen_iUnion fun a ↦ hs.preimage (by fun_prop) |>.inter <| ht.preimage (by fun_prop)

lemma IsOpen.relInv [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) : IsOpen s.inv :=
  hs.preimage continuous_swap

lemma IsOpen.relImage [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) {t : Set α} : IsOpen (s.image t) := by
  simp_rw [SetRel.image, ← exists_prop, Set.setOf_exists]
  exact isOpen_biUnion fun _ _ => hs.preimage <| .prodMk_right _

lemma IsOpen.relPreimage [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) {t : Set β} : IsOpen (s.preimage t) :=
  hs.relInv.relImage

lemma IsClosed.relInv [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) : IsClosed s.inv :=
  hs.preimage continuous_swap

lemma IsClosed.relImage_of_finite [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set α} (ht : t.Finite) : IsClosed (s.image t) := by
  simp_rw [SetRel.image, ← exists_prop, Set.setOf_exists]
  exact ht.isClosed_biUnion fun _ _ => hs.preimage <| .prodMk_right _

lemma IsClosed.relPreimage_of_finite [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set β} (ht : t.Finite) : IsClosed (s.preimage t) :=
  hs.relInv.relImage_of_finite ht

section UniformSpace

variable [UniformSpace α]

theorem eventually_uniformity_iterate_comp_subset {s : SetRel α α} (hs : s ∈ 𝓤 α) (n : ℕ) :
    ∀ᶠ t in (𝓤 α).smallSets, (t ○ ·)^[n] t ⊆ s := by
  suffices ∀ᶠ t in (𝓤 α).smallSets, t ⊆ s ∧ (t ○ ·)^[n] t ⊆ s from (eventually_and.1 this).2
  induction n generalizing s with
  | zero => simpa
  | succ _ ihn =>
    rcases comp_mem_uniformity_sets hs with ⟨t, htU, hts⟩
    refine (ihn htU).mono fun U hU => ?_
    rw [Function.iterate_succ_apply']
    have := isRefl_of_mem_uniformity htU
    exact ⟨hU.1.trans <| SetRel.left_subset_comp.trans hts,
     (SetRel.comp_subset_comp hU.1 hU.2).trans hts⟩

theorem eventually_uniformity_comp_subset {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∀ᶠ t in (𝓤 α).smallSets, t ○ t ⊆ s :=
  eventually_uniformity_iterate_comp_subset hs 1

/-!
### Balls in uniform spaces
-/

namespace UniformSpace

open UniformSpace (ball)

lemma isOpen_ball (x : α) {V : SetRel α α} (hV : IsOpen V) : IsOpen (ball x V) :=
  hV.preimage <| .prodMk_right _

lemma isClosed_ball (x : α) {V : SetRel α α} (hV : IsClosed V) : IsClosed (ball x V) :=
  hV.preimage <| .prodMk_right _

/-!
### Neighborhoods in uniform spaces
-/

theorem hasBasis_nhds_prod (x y : α) :
    HasBasis (𝓝 (x, y)) (fun s => s ∈ 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s ×ˢ ball y s := by
  rw [nhds_prod_eq]
  apply (hasBasis_nhds x).prod_same_index (hasBasis_nhds y)
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩
  exact ⟨U ∩ V, ⟨(𝓤 α).inter_sets U_in V_in, inferInstance⟩, ball_inter_left x U V,
    ball_inter_right y U V⟩

end UniformSpace

open UniformSpace

theorem nhds_eq_uniformity_prod {a b : α} :
    𝓝 (a, b) =
      (𝓤 α).lift' fun s : SetRel α α => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ s } := by
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift']
  · exact fun s => monotone_const.set_prod monotone_preimage
  · refine fun t => Monotone.set_prod ?_ monotone_const
    exact monotone_preimage (f := fun y => (y, a))

theorem nhdset_of_mem_uniformity {d : SetRel α α} (s : SetRel α α) (hd : d ∈ 𝓤 α) :
    ∃ t : SetRel α α, IsOpen t ∧ s ⊆ t ∧
      t ⊆ { p | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d } := by
  let cl_d := { p : α × α | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d }
  have : ∀ p ∈ s, ∃ t, t ⊆ cl_d ∧ IsOpen t ∧ p ∈ t := fun ⟨x, y⟩ hp =>
    mem_nhds_iff.mp <|
      show cl_d ∈ 𝓝 (x, y) by
        rw [nhds_eq_uniformity_prod, mem_lift'_sets]
        · exact ⟨d, hd, fun ⟨a, b⟩ ⟨ha, hb⟩ => ⟨x, y, ha, hp, hb⟩⟩
        · exact fun _ _ h _ h' => ⟨h h'.1, h h'.2⟩
  choose t ht using this
  exact ⟨(⋃ p : α × α, ⋃ h : p ∈ s, t p h : SetRel α α),
    isOpen_iUnion fun p : α × α => isOpen_iUnion fun hp => (ht p hp).right.left,
    fun ⟨a, b⟩ hp => by
      simp only [mem_iUnion, Prod.exists]; exact ⟨a, b, hp, (ht (a, b) hp).right.right⟩,
    iUnion_subset fun p => iUnion_subset fun hp => (ht p hp).left⟩

theorem nhds_le_uniformity (x : α) : 𝓝 (x, x) ≤ 𝓤 α := by
  intro V V_in
  rcases comp_symm_mem_uniformity_sets V_in with ⟨w, w_in, w_symm, w_sub⟩
  have : ball x w ×ˢ ball x w ∈ 𝓝 (x, x) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in)
  apply mem_of_superset this
  rintro ⟨u, v⟩ ⟨u_in, v_in⟩
  exact w_sub (mem_comp_of_mem_ball u_in v_in)

theorem iSup_nhds_le_uniformity : ⨆ x : α, 𝓝 (x, x) ≤ 𝓤 α :=
  iSup_le nhds_le_uniformity

theorem nhdsSet_diagonal_le_uniformity : 𝓝ˢ (diagonal α) ≤ 𝓤 α :=
  (nhdsSet_diagonal α).trans_le iSup_nhds_le_uniformity

variable (α)

theorem UniformSpace.has_seq_basis [IsCountablyGenerated <| 𝓤 α] :
    ∃ V : ℕ → SetRel α α, HasAntitoneBasis (𝓤 α) V ∧ ∀ n, SetRel.IsSymm (V n) :=
  let ⟨U, hsym, hbasis⟩ := (@UniformSpace.hasBasis_symmetric α _).exists_antitone_subbasis
  ⟨U, hbasis, fun n => (hsym n).2⟩

end

/-!
### Closure and interior in uniform spaces
-/

theorem closure_eq_uniformity (s : Set <| α × α) :
    closure s = ⋂ V ∈ {V | V ∈ 𝓤 α ∧ SetRel.IsSymm V}, V ○ s ○ V := by
  ext ⟨x, y⟩
  simp +contextual only
    [mem_closure_iff_nhds_basis (UniformSpace.hasBasis_nhds_prod x y), mem_iInter, mem_setOf_eq,
      and_imp, mem_comp_comp, ← mem_inter_iff, inter_comm, Set.Nonempty]

theorem uniformity_hasBasis_closed :
    HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α ∧ IsClosed V) id := by
  refine Filter.hasBasis_self.2 fun t h => ?_
  rcases comp_comp_symm_mem_uniformity_sets h with ⟨w, w_in, w_symm, r⟩
  refine ⟨closure w, mem_of_superset w_in subset_closure, isClosed_closure, ?_⟩
  refine Subset.trans ?_ r
  rw [closure_eq_uniformity]
  apply iInter_subset_of_subset
  apply iInter_subset
  exact ⟨w_in, w_symm⟩

theorem uniformity_eq_uniformity_closure : 𝓤 α = (𝓤 α).lift' closure :=
  Eq.symm <| uniformity_hasBasis_closed.lift'_closure_eq_self fun _ => And.right

theorem Filter.HasBasis.uniformity_closure {p : ι → Prop} {U : ι → SetRel α α}
    (h : (𝓤 α).HasBasis p U) : (𝓤 α).HasBasis p fun i => closure (U i) :=
  (@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure

theorem uniformity_hasBasis_closure : HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α) closure :=
  (𝓤 α).basis_sets.uniformity_closure

theorem closure_eq_inter_uniformity {t : SetRel α α} : closure t = ⋂ d ∈ 𝓤 α, d ○ (t ○ d) :=
  calc
    closure t = ⋂ (V) (_ : V ∈ 𝓤 α ∧ SetRel.IsSymm V), V ○ t ○ V := closure_eq_uniformity t
    _ = ⋂ V ∈ 𝓤 α, V ○ t ○ V :=
      Eq.symm <|
        UniformSpace.hasBasis_symmetric.biInter_mem fun _ _ hV => by dsimp at *; gcongr
    _ = ⋂ V ∈ 𝓤 α, V ○ (t ○ V) := by simp [SetRel.comp_assoc]

theorem uniformity_eq_uniformity_interior : 𝓤 α = (𝓤 α).lift' interior :=
  le_antisymm
    (le_iInf₂ fun d hd => by
      let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
      let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs
      have : s ⊆ interior d :=
        calc
          s ⊆ t := hst
          _ ⊆ interior d :=
            ht.subset_interior_iff.mpr fun x (hx : x ∈ t) =>
              let ⟨x, y, h₁, h₂, h₃⟩ := ht_comp hx
              hs_comp ⟨x, h₁, y, h₂, h₃⟩
      have : interior d ∈ 𝓤 α := by filter_upwards [hs] using this
      simp [this])
    fun _ hs => ((𝓤 α).lift' interior).sets_of_superset (mem_lift' hs) interior_subset

theorem interior_mem_uniformity {s : SetRel α α} (hs : s ∈ 𝓤 α) : interior s ∈ 𝓤 α := by
  rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs

theorem mem_uniformity_isClosed {s : SetRel α α} (h : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, IsClosed t ∧ t ⊆ s :=
  let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_hasBasis_closed.mem_iff.1 h
  ⟨t, ht_mem, htc, hts⟩

theorem closure_ball_subset {x : α} {V : SetRel α α} : closure (ball x V) ⊆ ball x (closure V) :=
  (Continuous.prodMk_right x).closure_preimage_subset V

theorem Dense.biUnion_uniformity_ball {s : Set α} {U : SetRel α α} (hs : Dense s) (hU : U ∈ 𝓤 α) :
    ⋃ x ∈ s, ball x U = univ := by
  refine iUnion₂_eq_univ_iff.2 fun y => ?_
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) ∈ U⟩
  exact ⟨x, hxs, hxy⟩

lemma DenseRange.iUnion_uniformity_ball {ι : Type*} {xs : ι → α}
    (xs_dense : DenseRange xs) {U : SetRel α α} (hU : U ∈ uniformity α) :
    ⋃ i, UniformSpace.ball (xs i) U = univ := by
  rw [← biUnion_range (f := xs) (g := fun x ↦ UniformSpace.ball x U)]
  exact Dense.biUnion_uniformity_ball xs_dense hU

/-!
### Uniformity bases
-/

theorem uniformity_hasBasis_open : HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α ∧ IsOpen V) id :=
  hasBasis_self.2 fun s hs =>
    ⟨interior s, interior_mem_uniformity hs, isOpen_interior, interior_subset⟩

theorem uniformity_hasBasis_open_symmetric :
    HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α ∧ IsOpen V ∧ SetRel.IsSymm V) id := by
  simp only [← and_assoc]
  refine uniformity_hasBasis_open.restrict fun s hs => ⟨SetRel.symmetrize s, ?_⟩
  exact
    ⟨⟨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.preimage continuous_swap)⟩,
      inferInstance, SetRel.symmetrize_subset_self⟩

theorem comp_open_symm_mem_uniformity_sets {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, IsOpen t ∧ SetRel.IsSymm t ∧ t ○ t ⊆ s := by
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u ⊆ t⟩ := uniformity_hasBasis_open_symmetric.mem_iff.mp ht₁
  exact ⟨u, hu₁, hu₂, hu₃, (SetRel.comp_subset_comp hu₄ hu₄).trans ht₂⟩

end UniformSpace

open uniformity

section Constructions

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

protected theorem UniformSpace.sInf_le {tt : Set (UniformSpace α)} {t : UniformSpace α}
    (h : t ∈ tt) : sInf tt ≤ t :=
  show ⨅ u ∈ tt, 𝓤[u] ≤ 𝓤[t] from iInf₂_le t h

protected theorem UniformSpace.le_sInf {tt : Set (UniformSpace α)} {t : UniformSpace α}
    (h : ∀ t' ∈ tt, t ≤ t') : t ≤ sInf tt :=
  show 𝓤[t] ≤ ⨅ u ∈ tt, 𝓤[u] from le_iInf₂ h

protected theorem UniformSpace.isGLB_sInf {tt : Set (UniformSpace α)} : IsGLB tt (sInf tt) :=
  ⟨fun _ ↦ UniformSpace.sInf_le, fun _ ↦ UniformSpace.le_sInf⟩

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

theorem iInf_uniformity {ι : Sort*} {u : ι → UniformSpace α} : 𝓤[iInf u] = ⨅ i, 𝓤[u i] :=
  iInf_range

-- INSTANCE (free from Core): inhabitedUniformSpace

-- INSTANCE (free from Core): inhabitedUniformSpaceCore

-- INSTANCE (free from Core): [Subsingleton

abbrev UniformSpace.comap (f : α → β) (u : UniformSpace β) : UniformSpace α where
  uniformity := 𝓤[u].comap fun p : α × α => (f p.1, f p.2)
  symm := by
    simp only [tendsto_comap_iff]
    exact tendsto_swap_uniformity.comp tendsto_comap
  comp := le_trans
    (by
      rw [comap_lift'_eq, comap_lift'_eq2]
      · exact lift'_mono' fun s _ ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩ => ⟨f x, h₁, h₂⟩
      · exact monotone_id.relComp monotone_id)
    (comap_mono u.comp)
  toTopologicalSpace := u.toTopologicalSpace.induced f
  nhds_eq_comap_uniformity x := by
    simp only [nhds_induced, nhds_eq_comap_uniformity, comap_comap, Function.comp_def]

lemma ball_preimage {f : α → β} {U : SetRel β β} {x : α} :
    UniformSpace.ball x (Prod.map f f ⁻¹' U) = f ⁻¹' UniformSpace.ball (f x) U := by
  ext : 1
  simp only [UniformSpace.ball, mem_preimage, Prod.map_apply]

set_option backward.isDefEq.respectTransparency false in
