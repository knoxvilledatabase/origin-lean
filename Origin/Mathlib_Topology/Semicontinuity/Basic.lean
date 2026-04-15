/-
Extracted from Topology/Semicontinuity/Basic.lean
Genuine: 37 of 38 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Lower and Upper Semicontinuity

This file develops key properties of upper and lower semicontinuous functions.

## Main definitions and results

We have some equivalent definitions of lower- and upper-semicontinuity (under certain
restrictions on the order on the codomain):
* `lowerSemicontinuous_iff_isOpen_preimage` in a linear order;
* `lowerSemicontinuous_iff_isClosed_preimage` in a linear order;
* `lowerSemicontinuousAt_iff_le_liminf` in a complete linear order;
* `lowerSemicontinuous_iff_isClosed_epigraph` in a linear order with the order
  topology.

We also prove:

* `indicator s (fun _ ↦ y)` is lower semicontinuous when `s` is open and `0 ≤ y`,
  or when `s` is closed and `y ≤ 0`;
* continuous functions are lower semicontinuous;
* left composition with a continuous monotone functions maps lower semicontinuous functions to lower
  semicontinuous functions. If the function is anti-monotone, it instead maps lower semicontinuous
  functions to upper semicontinuous functions;
* a sum of two (or finitely many) lower semicontinuous functions is lower semicontinuous;
* a supremum of a family of lower semicontinuous functions is lower semicontinuous;
* An infinite sum of `ℝ≥0∞`-valued lower semicontinuous functions is lower semicontinuous.

Similar results are stated and proved for upper semicontinuity.

We also prove that a function is continuous if and only if it is both lower and upper
semicontinuous.

## Implementation details

All the nontrivial results for upper semicontinuous functions are deduced from the corresponding
ones for lower semicontinuous functions using `OrderDual`.

## References

* <https://en.wikipedia.org/wiki/Closed_convex_function>
* <https://en.wikipedia.org/wiki/Semi-continuity>


+ lower and upper semicontinuity correspond to `r := (f · > ·)` and `r := (f · < ·)`;
+ lower and upper hemicontinuity correspond to `r := (fun x s ↦ IsOpen s ∧ ((f x) ∩ s).Nonempty)`
  and `r := (fun x s ↦ s ∈ 𝓝ˢ (f x))`, respectively.
-/

open Topology ENNReal

open Set Function Filter

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace γ] {f : α → β} {s t : Set α}
  {x : α} {y z : β}

/-! ### lower bounds -/

variable [LinearOrder β]

theorem LowerSemicontinuousOn.bddBelow_of_isCompact [Nonempty β] {s : Set α} (hs : IsCompact s)
    (hf : LowerSemicontinuousOn f s) : BddBelow (f '' s) := by
  cases s.eq_empty_or_nonempty with
  | inl h =>
      simp only [h, Set.image_empty]
      exact bddBelow_empty
  | inr h =>
      obtain ⟨a, _, has⟩ := LowerSemicontinuousOn.exists_isMinOn h hs hf
      exact has.bddBelow

end

/-! #### Indicators -/

variable [Zero β] [Preorder β]

theorem IsOpen.lowerSemicontinuous_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuous (indicator s fun _x => y) := by
  intro x z hz
  by_cases h : x ∈ s <;> simp [h] at hz
  · filter_upwards [hs.mem_nhds h]
    simp +contextual [hz]
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' ∈ s <;> simp [h', hz.trans_le hy, hz]

theorem IsOpen.lowerSemicontinuousOn_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t

theorem IsOpen.lowerSemicontinuousAt_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x

theorem IsOpen.lowerSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

theorem IsClosed.lowerSemicontinuous_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuous (indicator s fun _x => y) := by
  intro x z hz
  by_cases h : x ∈ s <;> simp [h] at hz
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' ∈ s <;> simp [h', hz, hz.trans_le hy]
  · filter_upwards [hs.isOpen_compl.mem_nhds h]
    simp +contextual [hz]

theorem IsClosed.lowerSemicontinuousOn_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t

theorem IsClosed.lowerSemicontinuousAt_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x

theorem IsClosed.lowerSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

end

/-! #### Relationship with continuity -/

variable [Preorder β]

theorem lowerSemicontinuous_iff_isOpen_preimage :
    LowerSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Ioi y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩

theorem LowerSemicontinuous.isOpen_preimage (hf : LowerSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Ioi y) :=
  lowerSemicontinuous_iff_isOpen_preimage.1 hf y

theorem lowerSemicontinuousOn_iff_preimage_Ioi :
    LowerSemicontinuousOn f s ↔ ∀ b, ∃ u, IsOpen u ∧ s ∩ f ⁻¹' Set.Ioi b = s ∩ u := by
  simp only [← lowerSemicontinuous_restrict_iff, restrict_eq,
    lowerSemicontinuous_iff_isOpen_preimage, preimage_comp, isOpen_induced_iff,
    Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

end

variable {ι : Type*} {f : ι → α → β} [Preorder β] {I : Set ι}

theorem lowerSemicontinuousOn_of_forall_isMaxOn_and_mem
    (hfy : ∀ i ∈ I, LowerSemicontinuousOn (f i) s)
    {M : α → ι}
    (M_mem : ∀ x ∈ s, M x ∈ I)
    (M_max : ∀ x ∈ s, IsMaxOn (fun y ↦ f y x) I (M x)) :
    LowerSemicontinuousOn (fun x ↦ f (M x) x) s := by
  intro x hx b hb
  apply Filter.Eventually.mp <| hfy (M x) (M_mem x hx) x hx b hb
  apply eventually_nhdsWithin_of_forall
  intro z hz h
  exact lt_of_lt_of_le h (M_max z hz (M_mem x hx))

theorem upperSemicontinuousOn_of_forall_isMinOn_and_mem
    (hfy : ∀ i ∈ I, UpperSemicontinuousOn (f i) s)
    {m : α → ι}
    (m_mem : ∀ x ∈ s, m x ∈ I)
    (m_min : ∀ x ∈ s, IsMinOn (fun i ↦ f i x) I (m x)) :
    UpperSemicontinuousOn (fun x ↦ f (m x) x) s :=
  lowerSemicontinuousOn_of_forall_isMaxOn_and_mem (β := βᵒᵈ) hfy m_mem m_min

end

variable {γ : Type*} [LinearOrder γ]

theorem lowerSemicontinuous_iff_isClosed_preimage {f : α → γ} :
    LowerSemicontinuous f ↔ ∀ y, IsClosed (f ⁻¹' Iic y) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Iic]

theorem LowerSemicontinuous.isClosed_preimage {f : α → γ} (hf : LowerSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Iic y) :=
  lowerSemicontinuous_iff_isClosed_preimage.1 hf y

theorem lowerSemicontinuousOn_iff_preimage_Iic {f : α → γ} :
    LowerSemicontinuousOn f s ↔ ∀ b, ∃ v, IsClosed v ∧ s ∩ f ⁻¹' Set.Iic b = s ∩ v := by
  simp only [← lowerSemicontinuous_restrict_iff, restrict_eq,
      lowerSemicontinuous_iff_isClosed_preimage, preimage_comp,
      isClosed_induced_iff, Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

variable [TopologicalSpace γ] [OrderTopology γ]

theorem ContinuousWithinAt.lowerSemicontinuousWithinAt {f : α → γ} (h : ContinuousWithinAt f s x) :
    LowerSemicontinuousWithinAt f s x := fun _y hy => h (Ioi_mem_nhds hy)

theorem ContinuousAt.lowerSemicontinuousAt {f : α → γ} (h : ContinuousAt f x) :
    LowerSemicontinuousAt f x := fun _y hy => h (Ioi_mem_nhds hy)

theorem ContinuousOn.lowerSemicontinuousOn {f : α → γ} (h : ContinuousOn f s) :
    LowerSemicontinuousOn f s := fun x hx => (h x hx).lowerSemicontinuousWithinAt

theorem Continuous.lowerSemicontinuous {f : α → γ} (h : Continuous f) : LowerSemicontinuous f :=
  fun _x => h.continuousAt.lowerSemicontinuousAt

end

/-! #### Equivalent definitions -/

variable {γ : Type*} [CompleteLinearOrder γ]

theorem lowerSemicontinuousWithinAt_iff_le_liminf {f : α → γ} :
    LowerSemicontinuousWithinAt f s x ↔ f x ≤ liminf f (𝓝[s] x) := by
  constructor
  · intro h; unfold LowerSemicontinuousWithinAt at h
    by_contra! hf
    obtain ⟨z, ltz, y, ylt, h₁⟩ := hf.exists_disjoint_Iio_Ioi
    exact ltz.not_ge
      (le_liminf_of_le (by isBoundedDefault) ((h y ylt).mono fun _ h₂ =>
        le_of_not_gt fun h₃ => (h₁ _ h₃ _ h₂).false))
  exact fun hf y ylt => eventually_lt_of_lt_liminf (ylt.trans_le hf)

alias ⟨LowerSemicontinuousWithinAt.le_liminf, _⟩ := lowerSemicontinuousWithinAt_iff_le_liminf

theorem lowerSemicontinuousAt_iff_le_liminf {f : α → γ} :
    LowerSemicontinuousAt f x ↔ f x ≤ liminf f (𝓝 x) := by
  rw [← lowerSemicontinuousWithinAt_univ_iff, lowerSemicontinuousWithinAt_iff_le_liminf,
    ← nhdsWithin_univ]

alias ⟨LowerSemicontinuousAt.le_liminf, _⟩ := lowerSemicontinuousAt_iff_le_liminf

theorem lowerSemicontinuous_iff_le_liminf {f : α → γ} :
    LowerSemicontinuous f ↔ ∀ x, f x ≤ liminf f (𝓝 x) := by
  simp only [← lowerSemicontinuousAt_iff_le_liminf, lowerSemicontinuous_iff]

alias ⟨LowerSemicontinuous.le_liminf, _⟩ := lowerSemicontinuous_iff_le_liminf

theorem lowerSemicontinuousOn_iff_le_liminf {f : α → γ} :
    LowerSemicontinuousOn f s ↔ ∀ x ∈ s, f x ≤ liminf f (𝓝[s] x) := by
  simp only [← lowerSemicontinuousWithinAt_iff_le_liminf, lowerSemicontinuousOn_iff]

alias ⟨LowerSemicontinuousOn.le_liminf, _⟩ := lowerSemicontinuousOn_iff_le_liminf

end

variable {γ : Type*} [LinearOrder γ]

theorem LowerSemicontinuousOn.isCompact_inter_preimage_Iic {f : α → γ}
    (hfs : LowerSemicontinuousOn f s) (ks : IsCompact s) (c : γ) :
    IsCompact (s ∩ f ⁻¹' Iic c) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfs
  obtain ⟨v, hv, hv'⟩ := hfs c
  exact hv' ▸ ks.inter_right hv

open scoped Set.Notation in

theorem LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset
    {ι : Type*} {f : ι → α → γ}
    (ks : IsCompact s) {I : Set ι} {c : γ} (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    s ∩ ⋂ i ∈ I, (f i) ⁻¹' Iic c = ∅ ↔ ∃ u : Finset I, ∀ x ∈ s, ∃ i ∈ u, c < f i x := by
  refine ⟨fun H ↦ ?_, fun ⟨u, hu⟩ ↦ ?_⟩
  · suffices ∀ i ∈ I, IsClosed (s ↓∩ (fun i ↦ f i ⁻¹' Iic c) i) by
      simpa [Set.eq_empty_iff_forall_notMem] using
        ks.elim_finite_subfamily_isClosed_subtype _ this H
    exact fun i hi ↦ lowerSemicontinuous_restrict_iff.mpr (hfi i hi) |>.isClosed_preimage c
  · rw [Set.eq_empty_iff_forall_notMem]
    simp only [mem_inter_iff, mem_iInter, mem_preimage, mem_Iic, not_and, not_forall,
      exists_prop, not_le]
    grind

variable [TopologicalSpace γ] [ClosedIciTopology γ]

theorem lowerSemicontinuousOn_iff_isClosed_epigraph {f : α → γ} {s : Set α} (hs : IsClosed s) :
    LowerSemicontinuousOn f s ↔ IsClosed {p : α × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  simp_rw [lowerSemicontinuousOn_iff, lowerSemicontinuousWithinAt_iff,
    eventually_nhdsWithin_iff, ← isOpen_compl_iff, compl_setOf, isOpen_iff_eventually, mem_setOf,
    not_and, not_le]
  constructor
  · intro hf ⟨x, y⟩ h
    by_cases hx : x ∈ s
    · have ⟨y', hy', z, hz, h₁⟩ := (h hx).exists_disjoint_Iio_Ioi
      filter_upwards [(hf x hx z hz).prodMk_nhds (eventually_lt_nhds hy')]
        with _ ⟨h₂, h₃⟩ h₄ using h₁ _ h₃ _ <| h₂ h₄
    · filter_upwards [(continuous_fst.tendsto _).eventually (hs.isOpen_compl.eventually_mem hx)]
        with _ h₁ h₂ using (h₁ h₂).elim
  · intro hf x _ y hy
    exact ((Continuous.prodMk_left y).tendsto x).eventually (hf (x, y) (fun _ => hy))

theorem lowerSemicontinuous_iff_isClosed_epigraph {f : α → γ} :
    LowerSemicontinuous f ↔ IsClosed {p : α × γ | f p.1 ≤ p.2} := by
  simp [← lowerSemicontinuousOn_univ_iff, lowerSemicontinuousOn_iff_isClosed_epigraph]

alias ⟨LowerSemicontinuous.isClosed_epigraph, _⟩ := lowerSemicontinuous_iff_isClosed_epigraph

end

/-! ### Composition -/

variable [Preorder β]

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]

variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]

variable {ι : Type*} [TopologicalSpace ι]

theorem ContinuousAt.comp_lowerSemicontinuousWithinAt {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Monotone g) :
    LowerSemicontinuousWithinAt (g ∘ f) s x := by
  intro y hy
  by_cases! h : ∃ l, l < f x
  · obtain ⟨z, zlt, hz⟩ : ∃ z < f x, Ioc z (f x) ⊆ g ⁻¹' Ioi y :=
      exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h
    filter_upwards [hf z zlt] with a ha
    calc
      y < g (min (f x) (f a)) := hz (by simp [zlt, ha])
      _ ≤ g (f a) := gmon (min_le_right _ _)
  · exact Filter.Eventually.of_forall fun a => hy.trans_le (gmon (h (f a)))

theorem ContinuousAt.comp_lowerSemicontinuousAt {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : LowerSemicontinuousAt f x) (gmon : Monotone g) : LowerSemicontinuousAt (g ∘ f) x := by
  simp only [← lowerSemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hg.comp_lowerSemicontinuousWithinAt hf gmon

theorem Continuous.comp_lowerSemicontinuousOn {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Monotone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt (hf x hx) gmon

theorem Continuous.comp_lowerSemicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Monotone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt (hf x) gmon

theorem ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  ContinuousAt.comp_lowerSemicontinuousWithinAt (δ := δᵒᵈ) hg hf gmon

theorem ContinuousAt.comp_lowerSemicontinuousAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousAt f x) (gmon : Antitone g) :
    UpperSemicontinuousAt (g ∘ f) x :=
  ContinuousAt.comp_lowerSemicontinuousAt (δ := δᵒᵈ) hg hf gmon

theorem Continuous.comp_lowerSemicontinuousOn_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Antitone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt_antitone (hf x hx) gmon

theorem Continuous.comp_lowerSemicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Antitone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt_antitone (hf x) gmon
