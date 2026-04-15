/-
Extracted from MeasureTheory/Function/Egorov.lean
Genuine: 18 of 18 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Egorov theorem

This file contains the Egorov theorem which states that an almost everywhere convergent
sequence on a finite measure space converges uniformly except on an arbitrarily small set.
This theorem is useful for the Vitali convergence theorem as well as theorems regarding
convergence in measure.

## Main results

* `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`: Egorov's theorem which shows that a sequence of
  almost everywhere convergent functions converges uniformly except on an arbitrarily small set.

-/

noncomputable section

open MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} [PseudoEMetricSpace β] {μ : Measure α}

namespace Egorov

def notConvergentSeq [Preorder ι] (f : ι → α → β) (g : α → β) (n : ℕ) (j : ι) : Set α :=
  ⋃ (k) (_ : j ≤ k), { x | (n : ℝ≥0∞)⁻¹ < edist (f k x) (g x) }

variable {n : ℕ} {j : ι} {s : Set α} {ε : ℝ} {f : ι → α → β} {g : α → β}

theorem mem_notConvergentSeq_iff [Preorder ι] {x : α} :
    x ∈ notConvergentSeq f g n j ↔ ∃ k ≥ j, (n : ℝ≥0∞)⁻¹ < edist (f k x) (g x) := by
  simp_rw [notConvergentSeq, Set.mem_iUnion, exists_prop, mem_setOf]

theorem notConvergentSeq_antitone [Preorder ι] : Antitone (notConvergentSeq f g n) :=
  fun _ _ hjk => Set.iUnion₂_mono' fun l hl => ⟨l, le_trans hjk hl, Set.Subset.rfl⟩

theorem measure_inter_notConvergentSeq_eq_zero [SemilatticeSup ι] [Nonempty ι]
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ ⋂ j, notConvergentSeq f g n j) = 0 := by
  simp_rw [EMetric.tendsto_atTop, ae_iff] at hfg
  rw [← nonpos_iff_eq_zero, ← hfg]
  refine measure_mono fun x => ?_
  simp only [Set.mem_inter_iff, Set.mem_iInter, mem_notConvergentSeq_iff]
  push Not
  rintro ⟨hmem, hx⟩
  refine ⟨hmem, (n : ℝ≥0∞)⁻¹, by simp, fun N => ?_⟩
  obtain ⟨n, hn₁, hn₂⟩ := hx N
  exact ⟨n, hn₁, hn₂.le⟩

theorem notConvergentSeq_measurableSet [Preorder ι] [Countable ι]
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a))) :
    MeasurableSet (notConvergentSeq f g n j) :=
  MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_lt measurable_const <| hf k

theorem measure_notConvergentSeq_tendsto_zero [SemilatticeSup ι] [Countable ι]
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a))) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    Tendsto (fun j => μ (s ∩ notConvergentSeq f g n j)) atTop (𝓝 0) := by
  rcases isEmpty_or_nonempty ι with h | h
  · have : (fun j => μ (s ∩ notConvergentSeq f g n j)) = fun j => 0 := by
      simp only [eq_iff_true_of_subsingleton]
    rw [this]
    exact tendsto_const_nhds
  rw [← measure_inter_notConvergentSeq_eq_zero hfg n, Set.inter_iInter]
  refine tendsto_measure_iInter_atTop
    (fun n ↦ (hsm.inter <| notConvergentSeq_measurableSet hf).nullMeasurableSet)
    (fun k l hkl => Set.inter_subset_inter_right _ <| notConvergentSeq_antitone hkl)
    ⟨h.some, ne_top_of_le_ne_top hs (measure_mono Set.inter_subset_left)⟩

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι]

theorem exists_notConvergentSeq_lt (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    ∃ j : ι, μ (s ∩ notConvergentSeq f g n j) ≤ ENNReal.ofReal (ε * 2⁻¹ ^ n) := by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop ENNReal.zero_ne_top).1
    (measure_notConvergentSeq_tendsto_zero hf hsm hs hfg n) (.ofReal (ε * 2⁻¹ ^ n))
      (by positivity)
  rw [zero_add] at hN
  exact ⟨N, (hN N le_rfl).2⟩

def notConvergentSeqLTIndex (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) : ι :=
  Classical.choose <| exists_notConvergentSeq_lt hε hf hsm hs hfg n

theorem notConvergentSeqLTIndex_spec (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ notConvergentSeq f g n (notConvergentSeqLTIndex hε hf hsm hs hfg n)) ≤
      ENNReal.ofReal (ε * 2⁻¹ ^ n) :=
  Classical.choose_spec <| exists_notConvergentSeq_lt hε hf hsm hs hfg n

def iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Set α :=
  ⋃ n, s ∩ notConvergentSeq f g n (notConvergentSeqLTIndex (half_pos hε) hf hsm hs hfg n)

theorem iUnionNotConvergentSeq_measurableSet (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MeasurableSet <| iUnionNotConvergentSeq hε hf hsm hs hfg :=
  MeasurableSet.iUnion fun _ ↦ hsm.inter <| notConvergentSeq_measurableSet hf

theorem measure_iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    μ (iUnionNotConvergentSeq hε hf hsm hs hfg) ≤ ENNReal.ofReal ε := by
  refine le_trans (measure_iUnion_le _) (le_trans
    (ENNReal.tsum_le_tsum <| notConvergentSeqLTIndex_spec (half_pos hε) hf hsm hs hfg) ?_)
  simp_rw [ENNReal.ofReal_mul (half_pos hε).le]
  rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg, inv_eq_one_div, tsum_geometric_two,
    ← ENNReal.ofReal_mul (half_pos hε).le, div_mul_cancel₀ ε two_ne_zero]
  · intro n; positivity
  · rw [inv_eq_one_div]
    exact summable_geometric_two

theorem iUnionNotConvergentSeq_subset (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    iUnionNotConvergentSeq hε hf hsm hs hfg ⊆ s := by
  rw [iUnionNotConvergentSeq, ← Set.inter_iUnion]
  exact Set.inter_subset_left

theorem tendstoUniformlyOn_diff_iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a))) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop (s \ Egorov.iUnionNotConvergentSeq hε hf hsm hs hfg) := by
  rw [EMetric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
  rw [eventually_atTop]
  refine ⟨Egorov.notConvergentSeqLTIndex (half_pos hε) hf hsm hs hfg N, fun n hn x hx => ?_⟩
  simp only [Set.mem_diff, Egorov.iUnionNotConvergentSeq, not_exists, Set.mem_iUnion,
    Set.mem_inter_iff, not_and, exists_and_left] at hx
  obtain ⟨hxs, hx⟩ := hx
  specialize hx hxs N
  rw [Egorov.mem_notConvergentSeq_iff] at hx
  push Not at hx
  rw [edist_comm]
  exact lt_of_le_of_lt (hx n hn) hN

end Egorov

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι]
  {f : ι → α → β} {g : α → β} {s : Set α}

theorem tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  ⟨Egorov.iUnionNotConvergentSeq hε hf hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_subset hε hf hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_measurableSet hε hf hsm hs hfg,
    Egorov.measure_iUnionNotConvergentSeq hε hf hsm hs hfg,
    Egorov.tendstoUniformlyOn_diff_iUnionNotConvergentSeq hε hf hsm hs hfg⟩

theorem tendstoUniformlyOn_of_ae_tendsto (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
    (fun n ↦ ((hf n).edist hg).measurable) hsm hs hfg hε

theorem tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' [IsFiniteMeasure μ]
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop tᶜ := by
  have ⟨t, _, ht, htendsto⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist hf MeasurableSet.univ
    (measure_ne_top μ Set.univ) (by filter_upwards [hfg] with _ htendsto _ using htendsto) hε
  refine ⟨_, ht, ?_⟩
  rwa [Set.compl_eq_univ_diff]

theorem tendstoUniformlyOn_of_ae_tendsto' [IsFiniteMeasure μ] (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ t, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop tᶜ :=
  tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' (fun n ↦ ((hf n).edist hg).measurable)
    hfg hε

end MeasureTheory
