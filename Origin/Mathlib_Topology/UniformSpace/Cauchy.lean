/-
Extracted from Topology/UniformSpace/Cauchy.lean
Genuine: 57 of 63 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Theory of Cauchy filters in uniform spaces. Complete uniform spaces. Totally bounded subsets.
-/

universe u v

open Filter Function TopologicalSpace Topology Set UniformSpace Uniformity

open scoped SetRel

variable {α : Type u} {β : Type v} [uniformSpace : UniformSpace α]

def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f ≤ 𝓤 α

def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x

theorem Filter.HasBasis.cauchy_iff {ι} {p : ι → Prop} {s : ι → SetRel α α} (h : (𝓤 α).HasBasis p s)
    {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ i, p i → ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, (x, y) ∈ s i :=
  and_congr Iff.rfl <|
    (f.basis_sets.prod_self.le_basis_iff h).trans <| by
      simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, id, forall_mem_comm]

theorem cauchy_iff' {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, (x, y) ∈ s :=
  (𝓤 α).basis_sets.cauchy_iff

theorem cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s :=
  cauchy_iff'.trans <| by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, forall_mem_comm]

lemma cauchy_iff_le {l : Filter α} [hl : l.NeBot] :
    Cauchy l ↔ l ×ˢ l ≤ 𝓤 α := by
  simp only [Cauchy, hl, true_and]

theorem cauchy_map_iff {l : Filter β} {f : β → α} :
    Cauchy (l.map f) ↔ NeBot l ∧ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α) := by
  rw [Cauchy, map_neBot_iff, prod_map_map_eq, Tendsto]

theorem cauchy_map_iff' {l : Filter β} [hl : NeBot l] {f : β → α} :
    Cauchy (l.map f) ↔ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α) :=
  cauchy_map_iff.trans <| and_iff_right hl

theorem Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f) (h_le : g ≤ f) : Cauchy g :=
  ⟨hg, le_trans (Filter.prod_mono h_le h_le) h_c.right⟩

theorem Cauchy.mono' {f g : Filter α} (h_c : Cauchy f) (_ : NeBot g) (h_le : g ≤ f) : Cauchy g :=
  h_c.mono h_le

theorem cauchy_nhds {a : α} : Cauchy (𝓝 a) :=
  ⟨nhds_neBot, nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)⟩

theorem cauchy_pure {a : α} : Cauchy (pure a) :=
  cauchy_nhds.mono (pure_le_nhds a)

theorem Filter.Tendsto.cauchy_map {l : Filter β} [NeBot l] {f : β → α} {a : α}
    (h : Tendsto f l (𝓝 a)) : Cauchy (map f l) :=
  cauchy_nhds.mono h

lemma Cauchy.mono_uniformSpace {u v : UniformSpace β} {F : Filter β} (huv : u ≤ v)
    (hF : Cauchy (uniformSpace := u) F) : Cauchy (uniformSpace := v) F :=
  ⟨hF.1, hF.2.trans huv⟩

lemma cauchy_inf_uniformSpace {u v : UniformSpace β} {F : Filter β} :
    Cauchy (uniformSpace := u ⊓ v) F ↔
    Cauchy (uniformSpace := u) F ∧ Cauchy (uniformSpace := v) F := by
  unfold Cauchy
  rw [inf_uniformity (u := u), le_inf_iff, and_and_left]

lemma cauchy_iInf_uniformSpace {ι : Sort*} [Nonempty ι] {u : ι → UniformSpace β}
    {l : Filter β} :
    Cauchy (uniformSpace := ⨅ i, u i) l ↔ ∀ i, Cauchy (uniformSpace := u i) l := by
  unfold Cauchy
  rw [iInf_uniformity, le_iInf_iff, forall_and, forall_const]

lemma cauchy_iInf_uniformSpace' {ι : Sort*} {u : ι → UniformSpace β}
    {l : Filter β} [l.NeBot] :
    Cauchy (uniformSpace := ⨅ i, u i) l ↔ ∀ i, Cauchy (uniformSpace := u i) l := by
  simp_rw [cauchy_iff_le (uniformSpace := _), iInf_uniformity, le_iInf_iff]

lemma cauchy_comap_uniformSpace {u : UniformSpace β} {α} {f : α → β} {l : Filter α} :
    Cauchy (uniformSpace := comap f u) l ↔ Cauchy (map f l) := by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap]
  rfl

lemma cauchy_prod_iff [UniformSpace β] {F : Filter (α × β)} :
    Cauchy F ↔ Cauchy (map Prod.fst F) ∧ Cauchy (map Prod.snd F) := by
  simp_rw +instances [instUniformSpaceProd, ← cauchy_comap_uniformSpace, ← cauchy_inf_uniformSpace]

theorem Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} (hf : Cauchy f) (hg : Cauchy g) :
    Cauchy (f ×ˢ g) := by
  have := hf.1; have := hg.1
  simpa [cauchy_prod_iff, hf.1] using ⟨hf, hg⟩

theorem le_nhds_of_cauchy_adhp_aux {f : Filter α} {x : α}
    (adhs : ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s ∧ ∃ y, (x, y) ∈ s ∧ y ∈ t) : f ≤ 𝓝 x := by
  -- Consider a neighborhood `s` of `x`
  intro s hs
  -- Take an entourage twice smaller than `s`
  rcases comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 hs) with ⟨U, U_mem, hU⟩
  -- Take a set `t ∈ f`, `t × t ⊆ U`, and a point `y ∈ t` such that `(x, y) ∈ U`
  rcases adhs U U_mem with ⟨t, t_mem, ht, y, hxy, hy⟩
  apply mem_of_superset t_mem
  -- Given a point `z ∈ t`, we have `(x, y) ∈ U` and `(y, z) ∈ t × t ⊆ U`, hence `z ∈ s`
  exact fun z hz => hU (SetRel.prodMk_mem_comp hxy (ht <| mk_mem_prod hy hz)) rfl

theorem le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (hf : Cauchy f) (adhs : ClusterPt x f) :
    f ≤ 𝓝 x :=
  le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      obtain ⟨t, t_mem, ht⟩ : ∃ t ∈ f, t ×ˢ t ⊆ s := (cauchy_iff.1 hf).2 s hs
      use t, t_mem, ht
      exact forall_mem_nonempty_iff_neBot.2 adhs _ (inter_mem_inf (mem_nhds_left x hs) t_mem))

theorem le_nhds_iff_adhp_of_cauchy {f : Filter α} {x : α} (hf : Cauchy f) :
    f ≤ 𝓝 x ↔ ClusterPt x f :=
  ⟨fun h => ClusterPt.of_le_nhds' h hf.1, le_nhds_of_cauchy_adhp hf⟩

protected theorem Cauchy.map [UniformSpace β] {f : Filter α} {m : α → β} (hf : Cauchy f)
    (hm : UniformContinuous m) : Cauchy (map m f) :=
  ⟨hf.1.map _,
    calc
      map m f ×ˢ map m f = map (Prod.map m m) (f ×ˢ f) := Filter.prod_map_map_eq
      _ ≤ Filter.map (Prod.map m m) (𝓤 α) := map_mono hf.right
      _ ≤ 𝓤 β := hm⟩

protected theorem Cauchy.comap [UniformSpace β] {f : Filter β} {m : α → β} (hf : Cauchy f)
    (hm : comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α) [NeBot (comap m f)] :
    Cauchy (comap m f) :=
  ⟨‹_›,
    calc
      comap m f ×ˢ comap m f = comap (Prod.map m m) (f ×ˢ f) := prod_comap_comap_eq
      _ ≤ comap (Prod.map m m) (𝓤 β) := comap_mono hf.right
      _ ≤ 𝓤 α := hm⟩

theorem Cauchy.comap' [UniformSpace β] {f : Filter β} {m : α → β} (hf : Cauchy f)
    (hm : Filter.comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α)
    (_ : NeBot (Filter.comap m f)) : Cauchy (Filter.comap m f) :=
  hf.comap hm

lemma Cauchy.map_of_le [UniformSpace β] {f : Filter α} {m : α → β} (hf : Cauchy f) {s : Set α}
    (hm : UniformContinuousOn m s) (hfs : f ≤ 𝓟 s) :
    Cauchy (map m f) := by
  suffices Cauchy (comap (Subtype.val : s → α) f) by
    simpa [Set.restrict_def, ← Function.comp_def, ← map_map,
      subtype_coe_map_comap, inf_eq_left.mpr hfs] using this.map hm.restrict
  exact hf.comap' (fun _ x ↦ x) (comap_coe_neBot_of_le_principal (h := hf.1) hfs)

def CauchySeq [Preorder β] (u : β → α) :=
  Cauchy (atTop.map u)

theorem CauchySeq.tendsto_uniformity [Preorder β] {u : β → α} (h : CauchySeq u) :
    Tendsto (Prod.map u u) atTop (𝓤 α) := by
  simpa only [Tendsto, prod_map_map_eq', prod_atTop_atTop_eq] using h.right

theorem CauchySeq.nonempty [Preorder β] {u : β → α} (hu : CauchySeq u) : Nonempty β :=
  @nonempty_of_neBot _ _ <| (map_neBot_iff _).1 hu.1

theorem Filter.Tendsto.cauchySeq [SemilatticeSup β] [Nonempty β] {f : β → α} {x}
    (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f :=
  hx.cauchy_map

theorem cauchySeq_const [SemilatticeSup β] [Nonempty β] (x : α) : CauchySeq fun _ : β => x :=
  tendsto_const_nhds.cauchySeq

theorem cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α) :=
  cauchy_map_iff'.trans <| by simp only [prod_atTop_atTop_eq, Prod.map_def]

theorem CauchySeq.comp_tendsto {γ} [Preorder β] [SemilatticeSup γ] [Nonempty γ] {f : β → α}
    (hf : CauchySeq f) {g : γ → β} (hg : Tendsto g atTop atTop) : CauchySeq (f ∘ g) :=
  ⟨inferInstance, le_trans (prod_le_prod.mpr ⟨Tendsto.comp le_rfl hg, Tendsto.comp le_rfl hg⟩) hf.2⟩

theorem CauchySeq.comp_injective [SemilatticeSup β] [NoMaxOrder β] [Nonempty β] {u : ℕ → α}
    (hu : CauchySeq u) {f : β → ℕ} (hf : Injective f) : CauchySeq (u ∘ f) :=
  hu.comp_tendsto <| Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite.mono_left atTop_le_cofinite

theorem Function.Bijective.cauchySeq_comp_iff {f : ℕ → ℕ} (hf : Bijective f) (u : ℕ → α) :
    CauchySeq (u ∘ f) ↔ CauchySeq u := by
  refine ⟨fun H => ?_, fun H => H.comp_injective hf.injective⟩
  lift f to ℕ ≃ ℕ using hf
  simpa only [Function.comp_def, f.apply_symm_apply] using H.comp_injective f.symm.injective

theorem CauchySeq.subseq_subseq_mem {V : ℕ → SetRel α α} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    (hu : CauchySeq u) {f g : ℕ → ℕ} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, ((u ∘ f ∘ φ) n, (u ∘ g ∘ φ) n) ∈ V n := by
  rw [cauchySeq_iff_tendsto] at hu
  exact ((hu.comp <| hf.prod_atTop hg).comp tendsto_atTop_diagonal).subseq_mem hV

theorem cauchySeq_iff' {u : ℕ → α} :
    CauchySeq u ↔ ∀ V ∈ 𝓤 α, ∀ᶠ k in atTop, k ∈ Prod.map u u ⁻¹' V :=
  cauchySeq_iff_tendsto

theorem cauchySeq_iff {u : ℕ → α} :
    CauchySeq u ↔ ∀ V ∈ 𝓤 α, ∃ N, ∀ k ≥ N, ∀ l ≥ N, (u k, u l) ∈ V := by
  simp only [cauchySeq_iff', Filter.eventually_atTop_prod_self', mem_preimage, Prod.map_apply]

theorem CauchySeq.prodMap {γ δ} [UniformSpace β] [Preorder γ] [Preorder δ] {u : γ → α} {v : δ → β}
    (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq (Prod.map u v) := by
  simpa only [CauchySeq, prod_map_map_eq', prod_atTop_atTop_eq] using hu.prod hv

theorem CauchySeq.prodMk {γ} [UniformSpace β] [Preorder γ] {u : γ → α} {v : γ → β}
    (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq fun x => (u x, v x) :=
  haveI := hu.1.of_map
  (Cauchy.prod hu hv).mono (tendsto_map.prodMk tendsto_map)

theorem CauchySeq.eventually_eventually [Preorder β] {u : β → α} (hu : CauchySeq u)
    {V : SetRel α α} (hV : V ∈ 𝓤 α) : ∀ᶠ k in atTop, ∀ᶠ l in atTop, (u k, u l) ∈ V :=
  eventually_atTop_curry <| hu.tendsto_uniformity hV

theorem UniformContinuous.comp_cauchySeq {γ} [UniformSpace β] [Preorder γ] {f : α → β}
    (hf : UniformContinuous f) {u : γ → α} (hu : CauchySeq u) : CauchySeq (f ∘ u) :=
  hu.map hf

theorem CauchySeq.subseq_mem {V : ℕ → SetRel α α} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    (hu : CauchySeq u) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, (u <| φ (n + 1), u <| φ n) ∈ V n := by
  have : ∀ n, ∃ N, ∀ k ≥ N, ∀ l ≥ k, (u l, u k) ∈ V n := fun n => by
    rw [cauchySeq_iff] at hu
    rcases hu _ (hV n) with ⟨N, H⟩
    exact ⟨N, fun k hk l hl => H _ (le_trans hk hl) _ hk⟩
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ∀ l ≥ φ n, (u l, u <| φ n) ∈ V n⟩ :=
    extraction_forall_of_eventually' this
  exact ⟨φ, φ_extr, fun n => hφ _ _ (φ_extr <| Nat.lt_add_one n).le⟩

theorem Filter.Tendsto.subseq_mem_entourage {V : ℕ → SetRel α α} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    {a : α} (hu : Tendsto u atTop (𝓝 a)) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ (u (φ 0), a) ∈ V 0 ∧
      ∀ n, (u <| φ (n + 1), u <| φ n) ∈ V (n + 1) := by
  rcases mem_atTop_sets.1 (hu (ball_mem_nhds a (symm_le_uniformity <| hV 0))) with ⟨n, hn⟩
  rcases (hu.comp (tendsto_add_atTop_nat n)).cauchySeq.subseq_mem fun n => hV (n + 1) with
    ⟨φ, φ_mono, hφV⟩
  exact ⟨fun k => φ k + n, φ_mono.add_const _, hn _ le_add_self, hφV⟩

theorem tendsto_nhds_of_cauchySeq_of_subseq [Preorder β] {u : β → α} (hu : CauchySeq u)
    {ι : Type*} {f : ι → β} {p : Filter ι} [NeBot p] (hf : Tendsto f p atTop) {a : α}
    (ha : Tendsto (u ∘ f) p (𝓝 a)) : Tendsto u atTop (𝓝 a) :=
  le_nhds_of_cauchy_adhp hu (ha.mapClusterPt.of_comp hf)

theorem Filter.HasBasis.cauchySeq_iff {γ} [Nonempty β] [SemilatticeSup β] {u : β → α} {p : γ → Prop}
    {s : γ → SetRel α α} (h : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ ∀ i, p i → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → (u m, u n) ∈ s i := by
  rw [cauchySeq_iff_tendsto, ← prod_atTop_atTop_eq]
  refine (atTop_basis.prod_self.tendsto_iff h).trans ?_
  simp only [true_and, Prod.forall, mem_prod_eq,
    mem_Ici, and_imp, Prod.map, @forall_comm (_ ≤ _) β]

theorem Filter.HasBasis.cauchySeq_iff' {γ} [Nonempty β] [SemilatticeSup β] {u : β → α}
    {p : γ → Prop} {s : γ → SetRel α α} (H : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ ∀ i, p i → ∃ N, ∀ n ≥ N, (u n, u N) ∈ s i := by
  refine H.cauchySeq_iff.trans ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · exact (h i hi).imp fun N hN n hn => hN n hn N le_rfl
  · rcases comp_symm_of_uniformity (H.mem_of_mem hi) with ⟨t, ht, ht', hts⟩
    rcases H.mem_iff.1 ht with ⟨j, hj, hjt⟩
    refine (h j hj).imp fun N hN m hm n hn => hts ⟨u N, hjt ?_, ht' <| hjt ?_⟩
    exacts [hN m hm, hN n hn]

theorem cauchySeq_of_controlled [SemilatticeSup β] [Nonempty β] (U : β → SetRel α α)
    (hU : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s) {f : β → α}
    (hf : ∀ ⦃N m n : β⦄, N ≤ m → N ≤ n → (f m, f n) ∈ U N) : CauchySeq f :=
  cauchySeq_iff_tendsto.2
    (by
      intro s hs
      rw [mem_map, mem_atTop_sets]
      obtain ⟨N, hN⟩ := hU s hs
      refine ⟨(N, N), fun mn hmn => ?_⟩
      obtain ⟨m, n⟩ := mn
      exact hN (hf hmn.1 hmn.2))

theorem isComplete_iff_clusterPt {s : Set α} :
    IsComplete s ↔ ∀ l, Cauchy l → l ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x l :=
  forall₃_congr fun _ hl _ => exists_congr fun _ => and_congr_right fun _ =>
    le_nhds_iff_adhp_of_cauchy hl

theorem isComplete_iff_ultrafilter {s : Set α} :
    IsComplete s ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → ↑l ≤ 𝓟 s → ∃ x ∈ s, ↑l ≤ 𝓝 x := by
  refine ⟨fun h l => h l, fun H => isComplete_iff_clusterPt.2 fun l hl hls => ?_⟩
  haveI := hl.1
  rcases H (Ultrafilter.of l) hl.ultrafilter_of ((Ultrafilter.of_le l).trans hls) with ⟨x, hxs, hxl⟩
  exact ⟨x, hxs, (ClusterPt.of_le_nhds hxl).mono (Ultrafilter.of_le l)⟩

theorem isComplete_iff_ultrafilter' {s : Set α} :
    IsComplete s ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → s ∈ l → ∃ x ∈ s, ↑l ≤ 𝓝 x :=
  isComplete_iff_ultrafilter.trans <| by simp only [le_principal_iff, Ultrafilter.mem_coe]

protected theorem IsComplete.union {s t : Set α} (hs : IsComplete s) (ht : IsComplete t) :
    IsComplete (s ∪ t) := by
  simp only [isComplete_iff_ultrafilter', Ultrafilter.union_mem_iff, or_imp] at *
  exact fun l hl =>
    ⟨fun hsl => (hs l hl hsl).imp fun x hx => ⟨Or.inl hx.1, hx.2⟩, fun htl =>
      (ht l hl htl).imp fun x hx => ⟨Or.inr hx.1, hx.2⟩⟩

theorem isComplete_iUnion_separated {ι : Sort*} {s : ι → Set α} (hs : ∀ i, IsComplete (s i))
    {U : SetRel α α} (hU : U ∈ 𝓤 α) (hd : ∀ (i j : ι), ∀ x ∈ s i, ∀ y ∈ s j, (x, y) ∈ U → i = j) :
    IsComplete (⋃ i, s i) := by
  set S := ⋃ i, s i
  intro l hl hls
  rw [le_principal_iff] at hls
  obtain ⟨hl_ne, hl'⟩ := cauchy_iff.1 hl
  obtain ⟨t, htS, htl, htU⟩ : ∃ t, t ⊆ S ∧ t ∈ l ∧ t ×ˢ t ⊆ U := by
    rcases hl' U hU with ⟨t, htl, htU⟩
    refine ⟨t ∩ S, inter_subset_right, inter_mem htl hls, Subset.trans ?_ htU⟩
    gcongr <;> apply inter_subset_left
  obtain ⟨i, hi⟩ : ∃ i, t ⊆ s i := by
    rcases Filter.nonempty_of_mem htl with ⟨x, hx⟩
    rcases mem_iUnion.1 (htS hx) with ⟨i, hi⟩
    refine ⟨i, fun y hy => ?_⟩
    rcases mem_iUnion.1 (htS hy) with ⟨j, hj⟩
    rwa [hd i j x hi y hj (htU <| mk_mem_prod hx hy)]
  rcases hs i l hl (le_principal_iff.2 <| mem_of_superset htl hi) with ⟨x, hxs, hlx⟩
  exact ⟨x, mem_iUnion.2 ⟨i, hxs⟩, hlx⟩

class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  /-- In a complete uniform space, every Cauchy filter converges. -/
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x

theorem complete_univ {α : Type u} [UniformSpace α] [CompleteSpace α] :
    IsComplete (univ : Set α) := fun f hf _ => by
  rcases CompleteSpace.complete hf with ⟨x, hx⟩
  exact ⟨x, mem_univ x, hx⟩

-- INSTANCE (free from Core): CompleteSpace.prod

lemma completeSpace_prod_of_nonempty [UniformSpace β] [Nonempty α] [Nonempty β] :
    CompleteSpace (α × β) ↔ CompleteSpace α ∧ CompleteSpace β :=
  ⟨fun _ ↦ ⟨.fst_of_prod (β := β), .snd_of_prod (α := α)⟩, fun ⟨_, _⟩ ↦ .prod⟩
