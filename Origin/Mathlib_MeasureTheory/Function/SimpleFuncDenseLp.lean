/-
Extracted from MeasureTheory/Function/SimpleFuncDenseLp.lean
Genuine: 20 of 27 | Dissolved: 7 | Infrastructure: 0
-/
import Origin.Core

/-!
# Density of simple functions

Show that each `Lᵖ` Borel measurable function can be approximated in `Lᵖ` norm
by a sequence of simple functions.

## Main definitions

* `MeasureTheory.Lp.simpleFunc`, the type of `Lp` simple functions
* `coeToLp`, the embedding of `Lp.simpleFunc E p μ` into `Lp E p μ`

## Main results

* `tendsto_approxOn_Lp_eLpNorm` (Lᵖ convergence): If `E` is a `NormedAddCommGroup` and `f` is
  measurable and `MemLp` (for `p < ∞`), then the simple functions
  `SimpleFunc.approxOn f hf s 0 h₀ n` may be considered as elements of `Lp E p μ`, and they tend
  in Lᵖ to `f`.
* `Lp.simpleFunc.isDenseEmbedding`: the embedding `coeToLp` of the `Lp` simple functions into
  `Lp` is dense.
* `Lp.simpleFunc.induction`, `Lp.induction`, `MemLp.induction`, `Integrable.induction`: to prove
  a predicate for all elements of one of these classes of functions, it suffices to check that it
  behaves correctly on simple functions.

## TODO

For `E` finite-dimensional, simple functions `α →ₛ E` are dense in L^∞ -- prove this.

## Notation

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
* `α →₁ₛ[μ] E`: the type of `L1` simple functions `α → β`.
-/

noncomputable section

open Set Function Filter TopologicalSpace ENNReal EMetric Finset

open scoped Topology ENNReal MeasureTheory

variable {α β ι E F 𝕜 : Type*}

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Lp approximation by simple functions -/

section Lp

variable [MeasurableSpace β] [MeasurableSpace E] [NormedAddCommGroup E] [NormedAddCommGroup F]
  {q : ℝ} {p : ℝ≥0∞}

theorem nnnorm_approxOn_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s y₀ h₀ n x - f x‖₊ ≤ ‖f x - y₀‖₊ := by
  have := edist_approxOn_le hf h₀ x n
  rw [edist_comm y₀] at this
  simp only [edist_nndist, nndist_eq_nnnorm] at this
  exact mod_cast this

theorem norm_approxOn_y₀_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s y₀ h₀ n x - y₀‖ ≤ ‖f x - y₀‖ + ‖f x - y₀‖ := by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using edist_approxOn_y0_le hf h₀ x n

theorem norm_approxOn_zero_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    (h₀ : (0 : E) ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s 0 h₀ n x‖ ≤ ‖f x‖ + ‖f x‖ := by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using edist_approxOn_y0_le hf h₀ x n

theorem tendsto_approxOn_Lp_eLpNorm [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (hp_ne_top : p ≠ ∞) {μ : Measure β}
    (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : eLpNorm (fun x => f x - y₀) p μ < ∞) :
    Tendsto (fun n => eLpNorm (⇑(approxOn f hf s y₀ h₀ n) - f) p μ) atTop (𝓝 0) := by
  by_cases hp_zero : p = 0
  · simpa only [hp_zero, eLpNorm_exponent_zero] using tendsto_const_nhds
  have hp : 0 < p.toReal := toReal_pos hp_zero hp_ne_top
  suffices Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) by
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_ne_top]
    convert continuous_rpow_const.continuousAt.tendsto.comp this
    simp [zero_rpow_of_pos (_root_.inv_pos.mpr hp)]
  -- We simply check the conditions of the Dominated Convergence Theorem:
  -- (1) The function "`p`-th power of distance between `f` and the approximation" is measurable
  have hF_meas n : Measurable fun x => ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal := by
    simpa only [← edist_eq_enorm_sub] using
      (approxOn f hf s y₀ h₀ n).measurable_bind (fun y x => edist y (f x) ^ p.toReal) fun y =>
        (measurable_edist_right.comp hf).pow_const p.toReal
  -- (2) The functions "`p`-th power of distance between `f` and the approximation" are uniformly
  -- bounded, at any given point, by `fun x => ‖f x - y₀‖ ^ p.toReal`
  have h_bound n :
    (fun x ↦ ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal) ≤ᵐ[μ] (‖f · - y₀‖ₑ ^ p.toReal) :=
    .of_forall fun x => rpow_le_rpow (coe_mono (nnnorm_approxOn_le hf h₀ x n)) toReal_nonneg
  -- (3) The bounding function `fun x => ‖f x - y₀‖ ^ p.toReal` has finite integral
  have h_fin : (∫⁻ a : β, ‖f a - y₀‖ₑ ^ p.toReal ∂μ) ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_ne_top hi).ne
  -- (4) The functions "`p`-th power of distance between `f` and the approximation" tend pointwise
  -- to zero
  have h_lim :
    ∀ᵐ a : β ∂μ, Tendsto (‖approxOn f hf s y₀ h₀ · a - f a‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    filter_upwards [hμ] with a ha
    have : Tendsto (fun n => (approxOn f hf s y₀ h₀ n) a - f a) atTop (𝓝 (f a - f a)) :=
      (tendsto_approxOn hf h₀ ha).sub tendsto_const_nhds
    convert continuous_rpow_const.continuousAt.tendsto.comp (tendsto_coe.mpr this.nnnorm)
    simp [zero_rpow_of_pos hp]
  -- Then we apply the Dominated Convergence Theorem
  simpa using tendsto_lintegral_of_dominated_convergence _ hF_meas h_bound h_fin h_lim

theorem memLp_approxOn [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    (hf : MemLp f p μ) {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (hi₀ : MemLp (fun _ => y₀) p μ) (n : ℕ) : MemLp (approxOn f fmeas s y₀ h₀ n) p μ := by
  refine ⟨(approxOn f fmeas s y₀ h₀ n).aestronglyMeasurable, ?_⟩
  suffices eLpNorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ < ⊤ by
    have : MemLp (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ :=
      ⟨(approxOn f fmeas s y₀ h₀ n - const β y₀).aestronglyMeasurable, this⟩
    convert eLpNorm_add_lt_top this hi₀
    ext x
    simp
  have hf' : MemLp (fun x => ‖f x - y₀‖) p μ := by
    have h_meas : Measurable fun x => ‖f x - y₀‖ := by
      simp only [← dist_eq_norm]
      fun_prop
    refine ⟨h_meas.aemeasurable.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_norm]
    convert eLpNorm_add_lt_top hf hi₀.neg with x
    simp [sub_eq_add_neg]
  have : ∀ᵐ x ∂μ, ‖approxOn f fmeas s y₀ h₀ n x - y₀‖ ≤ ‖‖f x - y₀‖ + ‖f x - y₀‖‖ := by
    filter_upwards with x
    convert norm_approxOn_y₀_le fmeas h₀ x n using 1
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  calc
    eLpNorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ ≤
        eLpNorm (fun x => ‖f x - y₀‖ + ‖f x - y₀‖) p μ :=
      eLpNorm_mono_ae this
    _ < ⊤ := eLpNorm_add_lt_top hf' hf'

theorem tendsto_approxOn_range_Lp_eLpNorm [BorelSpace E] {f : β → E} (hp_ne_top : p ≠ ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f ∪ {0} : Set E)]
    (hf : eLpNorm f p μ < ∞) :
    Tendsto (fun n => eLpNorm (⇑(approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) - f) p μ)
      atTop (𝓝 0) := by
  refine tendsto_approxOn_Lp_eLpNorm fmeas _ hp_ne_top ?_ ?_
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf

theorem memLp_approxOn_range [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f ∪ {0} : Set E)] (hf : MemLp f p μ) (n : ℕ) :
    MemLp (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) p μ :=
  memLp_approxOn fmeas hf (y₀ := 0) (by simp) MemLp.zero n

theorem tendsto_approxOn_range_Lp [BorelSpace E] {f : β → E} [hp : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f ∪ {0} : Set E)]
    (hf : MemLp f p μ) :
    Tendsto
      (fun n =>
        (memLp_approxOn_range fmeas hf n).toLp (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n))
      atTop (𝓝 (hf.toLp f)) := by
  simpa only [Lp.tendsto_Lp_iff_tendsto_eLpNorm''] using
    tendsto_approxOn_range_Lp_eLpNorm hp_ne_top fmeas hf.2

-- DISSOLVED: _root_.MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt

end Lp

/-! ### L1 approximation by simple functions -/

section Integrable

variable [MeasurableSpace β]

variable [MeasurableSpace E] [NormedAddCommGroup E]

theorem tendsto_approxOn_L1_enorm [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] {μ : Measure β}
    (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : HasFiniteIntegral (fun x => f x - y₀) μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ∂μ) atTop (𝓝 0) := by
  simpa [eLpNorm_one_eq_lintegral_enorm] using
    tendsto_approxOn_Lp_eLpNorm hf h₀ one_ne_top hμ
      (by simpa [eLpNorm_one_eq_lintegral_enorm] using hi)

theorem integrable_approxOn [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    (hf : Integrable f μ) {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (hi₀ : Integrable (fun _ => y₀) μ) (n : ℕ) : Integrable (approxOn f fmeas s y₀ h₀ n) μ := by
  rw [← memLp_one_iff_integrable] at hf hi₀ ⊢
  exact memLp_approxOn fmeas hf h₀ hi₀ n

theorem tendsto_approxOn_range_L1_enorm [OpensMeasurableSpace E] {f : β → E} {μ : Measure β}
    [SeparableSpace (range f ∪ {0} : Set E)] (fmeas : Measurable f) (hf : Integrable f μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f fmeas (range f ∪ {0}) 0 (by simp) n x - f x‖ₑ ∂μ) atTop
      (𝓝 0) := by
  apply tendsto_approxOn_L1_enorm fmeas
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf.2

theorem integrable_approxOn_range [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f ∪ {0} : Set E)] (hf : Integrable f μ) (n : ℕ) :
    Integrable (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) μ :=
  integrable_approxOn fmeas hf _ (integrable_zero _ _ _) n

end Integrable

section SimpleFuncProperties

variable [MeasurableSpace α]

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable {μ : Measure α} {p : ℝ≥0∞}

/-!
### Properties of simple functions in `Lp` spaces

A simple function `f : α →ₛ E` into a normed group `E` verifies, for a measure `μ`:
- `MemLp f 0 μ` and `MemLp f ∞ μ`, since `f` is a.e.-measurable and bounded,
- for `0 < p < ∞`,
  `MemLp f p μ ↔ Integrable f μ ↔ f.FinMeasSupp μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞`.
-/

theorem exists_forall_norm_le (f : α →ₛ F) : ∃ C, ∀ x, ‖f x‖ ≤ C :=
  exists_forall_le (f.map fun x => ‖x‖)

theorem memLp_zero (f : α →ₛ E) (μ : Measure α) : MemLp f 0 μ :=
  memLp_zero_iff_aestronglyMeasurable.mpr f.aestronglyMeasurable

theorem memLp_top (f : α →ₛ E) (μ : Measure α) : MemLp f ∞ μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
  memLp_top_of_bound f.aestronglyMeasurable C <| Eventually.of_forall hfC

protected theorem eLpNorm'_eq {p : ℝ} (f : α →ₛ F) (μ : Measure α) :
    eLpNorm' f p μ = (∑ y ∈ f.range, ‖y‖ₑ ^ p * μ (f ⁻¹' {y})) ^ (1 / p) := by
  have h_map : (‖f ·‖ₑ ^ p) = f.map (‖·‖ₑ ^ p) := by simp; rfl
  rw [eLpNorm'_eq_lintegral_enorm, h_map, lintegral_eq_lintegral, map_lintegral]

-- DISSOLVED: measure_preimage_lt_top_of_memLp

-- DISSOLVED: memLp_of_finite_measure_preimage

-- DISSOLVED: memLp_iff

-- DISSOLVED: integrable_iff

-- DISSOLVED: memLp_iff_integrable

-- DISSOLVED: memLp_iff_finMeasSupp

theorem integrable_iff_finMeasSupp {f : α →ₛ E} : Integrable f μ ↔ f.FinMeasSupp μ :=
  integrable_iff.trans finMeasSupp_iff.symm

theorem FinMeasSupp.integrable {f : α →ₛ E} (h : f.FinMeasSupp μ) : Integrable f μ :=
  integrable_iff_finMeasSupp.2 h

theorem integrable_pair {f : α →ₛ E} {g : α →ₛ F} :
    Integrable f μ → Integrable g μ → Integrable (pair f g) μ := by
  simpa only [integrable_iff_finMeasSupp] using FinMeasSupp.pair

theorem memLp_of_isFiniteMeasure (f : α →ₛ E) (p : ℝ≥0∞) (μ : Measure α) [IsFiniteMeasure μ] :
    MemLp f p μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
  MemLp.of_bound f.aestronglyMeasurable C <| Eventually.of_forall hfC
