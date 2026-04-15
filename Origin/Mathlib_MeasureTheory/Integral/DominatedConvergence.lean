/-
Extracted from MeasureTheory/Integral/DominatedConvergence.lean
Genuine: 24 of 25 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The dominated convergence theorem

This file collects various results related to the Lebesgue dominated convergence theorem
for the Bochner integral.

## Main results
- `MeasureTheory.tendsto_integral_of_dominated_convergence`:
  the Lebesgue dominated convergence theorem for the Bochner integral
- `MeasureTheory.hasSum_integral_of_dominated_convergence`:
  the Lebesgue dominated convergence theorem for series
- `MeasureTheory.integral_tsum`, `MeasureTheory.integral_tsum_of_summable_integral_norm`:
  the integral and `tsum`s commute, if the norms of the functions form a summable series
- `intervalIntegral.hasSum_integral_of_dominated_convergence`: the Lebesgue dominated convergence
  theorem for parametric interval integrals
- `intervalIntegral.continuous_of_dominated_interval`: continuity of the interval integral
  w.r.t. a parameter
- `intervalIntegral.continuous_primitive` and friends: primitives of interval integrable
  measurable functions are continuous

-/

open MeasureTheory Metric

/-!
## The Lebesgue dominated convergence theorem for the Bochner integral
-/

section DominatedConvergenceTheorem

open Set Filter TopologicalSpace ENNReal

open scoped Topology Interval

namespace MeasureTheory

variable {α E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {m : MeasurableSpace α} {μ : Measure α}

theorem tendsto_integral_of_dominated_convergence {F : ℕ → α → G} {f : α → G} (bound : α → ℝ)
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ) := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact tendsto_setToFun_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
      bound F_measurable bound_integrable h_bound h_lim
  · simp [integral, hG]

theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → G} {f : α → G} (bound : α → ℝ) (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) l (𝓝 <| ∫ a, f a ∂μ) := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact tendsto_setToFun_filter_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
      bound hF_meas h_bound bound_integrable h_lim
  · simp [integral, hG, tendsto_const_nhds]

theorem hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι → α → G} {f : α → G}
    (bound : ι → α → ℝ) (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound n a)
    (bound_summable : ∀ᵐ a ∂μ, Summable fun n => bound n a)
    (bound_integrable : Integrable (fun a => ∑' n, bound n a) μ)
    (h_lim : ∀ᵐ a ∂μ, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ) := by
  have hb_nonneg : ∀ᵐ a ∂μ, ∀ n, 0 ≤ bound n a :=
    eventually_countable_forall.2 fun n => (h_bound n).mono fun a => (norm_nonneg _).trans
  have hb_le_tsum : ∀ n, bound n ≤ᵐ[μ] fun a => ∑' n, bound n a := by
    intro n
    filter_upwards [hb_nonneg, bound_summable]
      with _ ha0 ha_sum using ha_sum.le_tsum _ fun i _ => ha0 i
  have hF_integrable : ∀ n, Integrable (F n) μ := by
    refine fun n => bound_integrable.mono' (hF_meas n) ?_
    exact EventuallyLE.trans (h_bound n) (hb_le_tsum n)
  simp only [HasSum, ← integral_finset_sum _ fun n _ => hF_integrable n]
  refine tendsto_integral_filter_of_dominated_convergence
      (fun a => ∑' n, bound n a) ?_ ?_ bound_integrable h_lim
  · exact Eventually.of_forall fun s => s.aestronglyMeasurable_fun_sum fun n _ => hF_meas n
  · filter_upwards with s
    filter_upwards [eventually_countable_forall.2 h_bound, hb_nonneg, bound_summable]
      with a hFa ha0 has
    calc
      ‖∑ n ∈ s, F n a‖ ≤ ∑ n ∈ s, bound n a := norm_sum_le_of_le _ fun n _ => hFa n
      _ ≤ ∑' n, bound n a := has.sum_le_tsum _ (fun n _ => ha0 n)

theorem integral_tsum {ι} [Countable ι] {f : ι → α → G} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ ≠ ∞) :
    ∫ a : α, ∑' i, f i a ∂μ = ∑' i, ∫ a : α, f i a ∂μ := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have hf'' i : AEMeasurable (‖f i ·‖ₑ) μ := (hf i).enorm
  have hhh : ∀ᵐ a : α ∂μ, Summable fun n => (‖f n a‖₊ : ℝ) := by
    rw [← lintegral_tsum hf''] at hf'
    refine (ae_lt_top' (AEMeasurable.ennreal_tsum hf'') hf').mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  convert (MeasureTheory.hasSum_integral_of_dominated_convergence (fun i a => ‖f i a‖₊) hf _ hhh
          ⟨_, _⟩ _).tsum_eq.symm
  · intro n
    filter_upwards with x
    rfl
  · simp_rw [← NNReal.coe_tsum]
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.coe_nnreal_real
    apply AEMeasurable.nnreal_tsum
    exact fun i => (hf i).nnnorm.aemeasurable
  · dsimp [HasFiniteIntegral]
    have : ∫⁻ a, ∑' n, ‖f n a‖ₑ ∂μ < ⊤ := by rwa [lintegral_tsum hf'', lt_top_iff_ne_top]
    convert this using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm, NNReal.nnnorm_eq]
    filter_upwards [hhh] with a ha
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp ha)
  · filter_upwards [hhh] with x hx
    exact hx.of_norm.hasSum

lemma hasSum_integral_of_summable_integral_norm {ι} [Countable ι] {F : ι → α → E}
    (hF_int : ∀ i : ι, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    HasSum (∫ a, F · a ∂μ) (∫ a, (∑' i, F i a) ∂μ) := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, hasSum_zero]
  rw [integral_tsum (fun i ↦ (hF_int i).1)]
  · exact (hF_sum.of_norm_bounded fun i ↦ norm_integral_le_integral_norm _).hasSum
  have (i : ι) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF_int i).norm, coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun a ↦ norm_nonneg (F i a)))]
    simp only [coe_nnnorm]
  rw [funext this]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hF_sum.abs

lemma integral_tsum_of_summable_integral_norm {ι} [Countable ι] {F : ι → α → E}
    (hF_int : ∀ i : ι, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    ∑' i, (∫ a, F i a ∂μ) = ∫ a, (∑' i, F i a) ∂μ :=
  (hasSum_integral_of_summable_integral_norm hF_int hF_sum).tsum_eq

theorem tendsto_integral_filter_of_norm_le_const {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → G} [IsFiniteMeasure μ] {f : α → G}
    (h_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∃ C, ∀ᶠ n in l, (∀ᵐ ω ∂μ, ‖F n ω‖ ≤ C))
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) l (𝓝 (f ω))) :
    Tendsto (fun n => ∫ ω, F n ω ∂μ) l (nhds (∫ ω, f ω ∂μ)) := by
  obtain ⟨c, h_boundc⟩ := h_bound
  let C : α → ℝ := (fun _ => c)
  exact tendsto_integral_filter_of_dominated_convergence
    C h_meas h_boundc (integrable_const c) h_lim

end MeasureTheory

section TendstoMono

variable {α E : Type*} [MeasurableSpace α]
  {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : ℕ → Set α}
  {f : α → E}

theorem _root_.Antitone.tendsto_setIntegral (hsm : ∀ i, MeasurableSet (s i)) (h_anti : Antitone s)
    (hfi : IntegrableOn f (s 0) μ) :
    Tendsto (fun i => ∫ a in s i, f a ∂μ) atTop (𝓝 (∫ a in ⋂ n, s n, f a ∂μ)) := by
  let bound : α → ℝ := indicator (s 0) fun a => ‖f a‖
  have h_int_eq : (fun i => ∫ a in s i, f a ∂μ) = fun i => ∫ a, (s i).indicator f a ∂μ :=
    funext fun i => (integral_indicator (hsm i)).symm
  rw [h_int_eq]
  rw [← integral_indicator (MeasurableSet.iInter hsm)]
  refine tendsto_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_
  · intro n
    rw [aestronglyMeasurable_indicator_iff (hsm n)]
    exact (IntegrableOn.mono_set hfi (h_anti (zero_le n))).1
  · rw [integrable_indicator_iff (hsm 0)]
    exact hfi.norm
  · simp_rw [norm_indicator_eq_indicator_norm]
    refine fun n => Eventually.of_forall fun x => ?_
    grw [(h_anti (zero_le n)).subset]
  · filter_upwards [] with a using le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)

end TendstoMono

/-!
## The Lebesgue dominated convergence theorem for interval integrals
As an application, we show continuity of parametric integrals.
-/

namespace intervalIntegral

section DCT

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ → E} {μ : Measure ℝ}

nonrec theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → ℝ → E} (bound : ℝ → ℝ)
    (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) (μ.restrict (Ι a b)))
    (h_bound : ∀ᶠ n in l, ∀ᵐ x ∂μ, x ∈ Ι a b → ‖F n x‖ ≤ bound x)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_lim : ∀ᵐ x ∂μ, x ∈ Ι a b → Tendsto (fun n => F n x) l (𝓝 (f x))) :
    Tendsto (fun n => ∫ x in a..b, F n x ∂μ) l (𝓝 <| ∫ x in a..b, f x ∂μ) := by
  simp only [intervalIntegrable_iff, intervalIntegral_eq_integral_uIoc,
    ← ae_restrict_iff' (α := ℝ) (μ := μ) measurableSet_uIoc] at *
  exact tendsto_const_nhds.smul <|
    tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_lim

nonrec theorem hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι → ℝ → E}
    (bound : ι → ℝ → ℝ) (hF_meas : ∀ n, AEStronglyMeasurable (F n) (μ.restrict (Ι a b)))
    (h_bound : ∀ n, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F n t‖ ≤ bound n t)
    (bound_summable : ∀ᵐ t ∂μ, t ∈ Ι a b → Summable fun n => bound n t)
    (bound_integrable : IntervalIntegrable (fun t => ∑' n, bound n t) μ a b)
    (h_lim : ∀ᵐ t ∂μ, t ∈ Ι a b → HasSum (fun n => F n t) (f t)) :
    HasSum (fun n => ∫ t in a..b, F n t ∂μ) (∫ t in a..b, f t ∂μ) := by
  simp only [intervalIntegrable_iff, intervalIntegral_eq_integral_uIoc, ←
    ae_restrict_iff' (α := ℝ) (μ := μ) measurableSet_uIoc] at *
  exact
    (hasSum_integral_of_dominated_convergence bound hF_meas h_bound bound_summable bound_integrable
          h_lim).const_smul
      _

theorem hasSum_intervalIntegral_of_summable_norm [Countable ι] {f : ι → C(ℝ, E)}
    (hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ)‖) :
    HasSum (fun i : ι => ∫ x in a..b, f i x) (∫ x in a..b, ∑' i : ι, f i x) := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE, hasSum_zero]
  apply hasSum_integral_of_dominated_convergence
    (fun i (x : ℝ) => ‖(f i).restrict ↑(⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ)‖)
    (fun i => (map_continuous <| f i).aestronglyMeasurable)
  · intro i; filter_upwards with x hx
    apply ContinuousMap.norm_coe_le_norm ((f i).restrict _) ⟨x, _⟩
    exact ⟨hx.1.le, hx.2⟩
  · exact ae_of_all _ fun x _ => hf_sum
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun x hx => Summable.hasSum ?_
    let x : (⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ) := ⟨x, ⟨hx.1.le, hx.2⟩⟩
    have := hf_sum.of_norm
    simpa only [Compacts.coe_mk, ContinuousMap.restrict_apply]
      using ContinuousMap.summable_apply this x

theorem tsum_intervalIntegral_eq_of_summable_norm [Countable ι] {f : ι → C(ℝ, E)}
    (hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ)‖) :
    ∑' i : ι, ∫ x in a..b, f i x = ∫ x in a..b, ∑' i : ι, f i x :=
  (hasSum_intervalIntegral_of_summable_norm hf_sum).tsum_eq

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

theorem continuousWithinAt_of_dominated_interval {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ}
    {s : Set X} (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → ContinuousWithinAt (fun x => F x t) s x₀) :
    ContinuousWithinAt (fun x => ∫ t in a..b, F x t ∂μ) s x₀ :=
  tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

theorem continuousAt_of_dominated_interval {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → ContinuousAt (fun x => F x t) x₀) :
    ContinuousAt (fun x => ∫ t in a..b, F x t ∂μ) x₀ :=
  tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

theorem continuous_of_dominated_interval {F : X → ℝ → E} {bound : ℝ → ℝ} {a b : ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) <| μ.restrict <| Ι a b)
    (h_bound : ∀ x, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → Continuous fun x => F x t) :
    Continuous fun x => ∫ t in a..b, F x t ∂μ :=
  continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_of_dominated_interval (Eventually.of_forall hF_meas) (Eventually.of_forall h_bound)
        bound_integrable <|
      h_cont.mono fun _ himp hx => (himp hx).continuousAt

end DCT

section ContinuousPrimitive

open scoped Interval

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
  {a b b₀ b₁ b₂ : ℝ} {μ : Measure ℝ} {f : ℝ → E}

theorem continuousWithinAt_primitive (hb₀ : μ {b₀} = 0)
    (h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)) :
    ContinuousWithinAt (fun b => ∫ x in a..b, f x ∂μ) (Icc b₁ b₂) b₀ := by
  by_cases h₀ : b₀ ∈ Icc b₁ b₂
  · have h₁₂ : b₁ ≤ b₂ := h₀.1.trans h₀.2
    have min₁₂ : min b₁ b₂ = b₁ := min_eq_left h₁₂
    have h_int' : ∀ {x}, x ∈ Icc b₁ b₂ → IntervalIntegrable f μ b₁ x := by
      rintro x ⟨h₁, h₂⟩
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_right a b₁),
          h₁.trans (h₂.trans <| le_max_of_le_right <| le_max_right _ _)⟩
      · exact ⟨min_le_of_left_le <| (min_le_right _ _).trans h₁,
          le_max_of_le_right <| h₂.trans <| le_max_right _ _⟩
    have : ∀ b ∈ Icc b₁ b₂,
        ∫ x in a..b, f x ∂μ = (∫ x in a..b₁, f x ∂μ) + ∫ x in b₁..b, f x ∂μ := by
      rintro b ⟨h₁, h₂⟩
      rw [← integral_add_adjacent_intervals _ (h_int' ⟨h₁, h₂⟩)]
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_left a b₁), le_max_of_le_right (le_max_left _ _)⟩
      · exact ⟨min_le_of_left_le (min_le_right _ _),
          le_max_of_le_right (h₁.trans <| h₂.trans (le_max_right a b₂))⟩
    apply ContinuousWithinAt.congr _ this (this _ h₀); clear this
    refine continuousWithinAt_const.add ?_
    have :
      (fun b => ∫ x in b₁..b, f x ∂μ) =ᶠ[𝓝[Icc b₁ b₂] b₀] fun b =>
        ∫ x in b₁..b₂, indicator {x | x ≤ b} f x ∂μ := by
      apply eventuallyEq_of_mem self_mem_nhdsWithin
      exact fun b b_in => (integral_indicator b_in).symm
    apply ContinuousWithinAt.congr_of_eventuallyEq _ this (integral_indicator h₀).symm
    have : IntervalIntegrable (fun x => ‖f x‖) μ b₁ b₂ :=
      IntervalIntegrable.norm (h_int' <| right_mem_Icc.mpr h₁₂)
    refine continuousWithinAt_of_dominated_interval ?_ ?_ this ?_ <;> clear this
    · filter_upwards [self_mem_nhdsWithin]
      intro x hx
      rw [aestronglyMeasurable_indicator_iff, Measure.restrict_restrict, uIoc, Iic_def,
        Iic_inter_Ioc_of_le]
      · rw [min₁₂]
        exact (h_int' hx).1.aestronglyMeasurable
      · exact le_max_of_le_right hx.2
      exacts [measurableSet_Iic, measurableSet_Iic]
    · filter_upwards with x; filter_upwards with t
      dsimp [indicator]
      split_ifs <;> simp
    · have : ∀ᵐ t ∂μ, t < b₀ ∨ b₀ < t := by
        filter_upwards [compl_mem_ae_iff.mpr hb₀] with x hx using Ne.lt_or_gt hx
      apply this.mono
      rintro x₀ (hx₀ | hx₀) -
      · have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : ℝ | t ≤ x}.indicator f x₀ = f x₀ := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Ioi_mem_nhds hx₀)
          intro x hx
          simp [hx.le]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀.le]
      · have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : ℝ | t ≤ x}.indicator f x₀ = 0 := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Iio_mem_nhds hx₀)
          intro x hx
          simp [hx]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀]
  · apply continuousWithinAt_of_notMem_closure
    rwa [closure_Icc]

theorem continuousAt_parametric_primitive_of_dominated [FirstCountableTopology X]
    {F : X → ℝ → E} (bound : ℝ → ℝ) (a b : ℝ)
    {a₀ b₀ : ℝ} {x₀ : X} (hF_meas : ∀ x, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂μ.restrict <| Ι a b, ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ.restrict <| Ι a b, ContinuousAt (fun x ↦ F x t) x₀) (ha₀ : a₀ ∈ Ioo a b)
    (hb₀ : b₀ ∈ Ioo a b) (hμb₀ : μ {b₀} = 0) :
    ContinuousAt (fun p : X × ℝ ↦ ∫ t : ℝ in a₀..p.2, F p.1 t ∂μ) (x₀, b₀) := by
  have hsub : ∀ {a₀ b₀}, a₀ ∈ Ioo a b → b₀ ∈ Ioo a b → Ι a₀ b₀ ⊆ Ι a b := fun ha₀ hb₀ ↦
    (ordConnected_Ioo.uIoc_subset ha₀ hb₀).trans (Ioo_subset_Ioc_self.trans Ioc_subset_uIoc)
  have Ioo_nhds : Ioo a b ∈ 𝓝 b₀ := Ioo_mem_nhds hb₀.1 hb₀.2
  have Icc_nhds : Icc a b ∈ 𝓝 b₀ := Icc_mem_nhds hb₀.1 hb₀.2
  have hx₀ : ∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x₀ t‖ ≤ bound t := h_bound.self_of_nhds
  have : ∀ᶠ p : X × ℝ in 𝓝 (x₀, b₀),
      ∫ s in a₀..p.2, F p.1 s ∂μ =
        ∫ s in a₀..b₀, F p.1 s ∂μ + ∫ s in b₀..p.2, F x₀ s ∂μ +
          ∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ := by
    rw [nhds_prod_eq]
    refine (h_bound.prod_mk Ioo_nhds).mono ?_
    rintro ⟨x, t⟩ ⟨hx : ∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t, ht : t ∈ Ioo a b⟩
    dsimp
    have hiF : ∀ {x a₀ b₀},
        (∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t) → a₀ ∈ Ioo a b → b₀ ∈ Ioo a b →
          IntervalIntegrable (F x) μ a₀ b₀ := fun {x a₀ b₀} hx ha₀ hb₀ ↦
      (bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀).mono_fun'
        ((hF_meas x).mono_set <| hsub ha₀ hb₀)
        (ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
    rw [intervalIntegral.integral_sub, add_assoc, add_sub_cancel,
      intervalIntegral.integral_add_adjacent_intervals]
    · exact hiF hx ha₀ hb₀
    · exact hiF hx hb₀ ht
    · exact hiF hx hb₀ ht
    · exact hiF hx₀ hb₀ ht
  rw [continuousAt_congr this]; clear this
  refine (ContinuousAt.add ?_ ?_).add ?_
  · exact (intervalIntegral.continuousAt_of_dominated_interval
        (Eventually.of_forall fun x ↦ (hF_meas x).mono_set <| hsub ha₀ hb₀)
          (h_bound.mono fun x hx ↦
            ae_imp_of_ae_restrict <| ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
          (bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀) <|
          ae_imp_of_ae_restrict <| ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) h_cont).fst'
  · refine (?_ : ContinuousAt (fun t ↦ ∫ s in b₀..t, F x₀ s ∂μ) b₀).snd'
    apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₀.1 hb₀.2)
    apply intervalIntegral.continuousWithinAt_primitive hμb₀
    rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le]
    exact bound_integrable.mono_fun' (hF_meas x₀) hx₀
  · suffices Tendsto (fun x : X × ℝ ↦ ∫ s in b₀..x.2, F x.1 s - F x₀ s ∂μ) (𝓝 (x₀, b₀)) (𝓝 0) by
      simpa [ContinuousAt]
    have : ∀ᶠ p : X × ℝ in 𝓝 (x₀, b₀),
        ‖∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ‖ ≤ |∫ s in b₀..p.2, 2 * bound s ∂μ| := by
      rw [nhds_prod_eq]
      refine (h_bound.prod_mk Ioo_nhds).mono ?_
      rintro ⟨x, t⟩ ⟨hx : ∀ᵐ t ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t, ht : t ∈ Ioo a b⟩
      have H : ∀ᵐ t : ℝ ∂μ.restrict (Ι b₀ t), ‖F x t - F x₀ t‖ ≤ 2 * bound t := by
        apply (ae_restrict_of_ae_restrict_of_subset (hsub hb₀ ht) (hx.and hx₀)).mono
        rintro s ⟨hs₁, hs₂⟩
        calc
          ‖F x s - F x₀ s‖ ≤ ‖F x s‖ + ‖F x₀ s‖ := norm_sub_le _ _
          _ ≤ 2 * bound s := by linarith only [hs₁, hs₂]
      exact intervalIntegral.norm_integral_le_abs_of_norm_le H
        ((bound_integrable.mono_set' <| hsub hb₀ ht).const_mul 2)
    apply squeeze_zero_norm' this
    have : Tendsto (fun t ↦ ∫ s in b₀..t, 2 * bound s ∂μ) (𝓝 b₀) (𝓝 0) := by
      suffices ContinuousAt (fun t ↦ ∫ s in b₀..t, 2 * bound s ∂μ) b₀ by
        simpa [ContinuousAt] using this
      apply ContinuousWithinAt.continuousAt _ Icc_nhds
      apply intervalIntegral.continuousWithinAt_primitive hμb₀
      apply IntervalIntegrable.const_mul
      apply bound_integrable.mono_set'
      rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le]
    rw [nhds_prod_eq]
    exact (continuous_abs.tendsto' _ _ abs_zero).comp (this.comp tendsto_snd)

variable [NoAtoms μ]

theorem continuousOn_primitive (h_int : IntegrableOn f (Icc a b) μ) :
    ContinuousOn (fun x => ∫ t in Ioc a x, f t ∂μ) (Icc a b) := by
  by_cases h : a ≤ b
  · have : ∀ x ∈ Icc a b, ∫ t in Ioc a x, f t ∂μ = ∫ t in a..x, f t ∂μ := by
      intro x x_in
      simp_rw [integral_of_le x_in.1]
    rw [continuousOn_congr this]
    intro x₀ _
    refine continuousWithinAt_primitive (measure_singleton x₀) ?_
    simp only [intervalIntegrable_iff_integrableOn_Ioc_of_le, max_eq_right, h, min_self]
    exact h_int.mono Ioc_subset_Icc_self le_rfl
  · rw [Icc_eq_empty h]
    exact continuousOn_empty _

theorem continuousOn_primitive_Icc (h_int : IntegrableOn f (Icc a b) μ) :
    ContinuousOn (fun x => ∫ t in Icc a x, f t ∂μ) (Icc a b) := by
  have aux : (fun x => ∫ t in Icc a x, f t ∂μ) = fun x => ∫ t in Ioc a x, f t ∂μ := by
    ext x
    exact integral_Icc_eq_integral_Ioc
  rw [aux]
  exact continuousOn_primitive h_int

theorem continuousOn_primitive_interval' (h_int : IntervalIntegrable f μ b₁ b₂)
    (ha : a ∈ [[b₁, b₂]]) : ContinuousOn (fun b => ∫ x in a..b, f x ∂μ) [[b₁, b₂]] := fun _ _ ↦ by
  refine continuousWithinAt_primitive (measure_singleton _) ?_
  rw [min_eq_right ha.1, max_eq_right ha.2]
  simpa [intervalIntegrable_iff, uIoc] using h_int

theorem continuousOn_primitive_interval (h_int : IntegrableOn f (uIcc a b) μ) :
    ContinuousOn (fun x => ∫ t in a..x, f t ∂μ) (uIcc a b) :=
  continuousOn_primitive_interval' h_int.intervalIntegrable left_mem_uIcc

theorem continuousOn_primitive_interval_left (h_int : IntegrableOn f (uIcc a b) μ) :
    ContinuousOn (fun x => ∫ t in x..b, f t ∂μ) (uIcc a b) := by
  rw [uIcc_comm a b] at h_int ⊢
  simp only [integral_symm b]
  exact (continuousOn_primitive_interval h_int).neg

theorem continuous_primitive (h_int : ∀ a b, IntervalIntegrable f μ a b) (a : ℝ) :
    Continuous fun b => ∫ x in a..b, f x ∂μ := by
  rw [continuous_iff_continuousAt]
  intro b₀
  obtain ⟨b₁, hb₁⟩ := exists_lt b₀
  obtain ⟨b₂, hb₂⟩ := exists_gt b₀
  apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₁ hb₂)
  exact continuousWithinAt_primitive (measure_singleton b₀) (h_int _ _)

nonrec theorem _root_.MeasureTheory.Integrable.continuous_primitive (h_int : Integrable f μ)
    (a : ℝ) : Continuous fun b => ∫ x in a..b, f x ∂μ :=
  continuous_primitive (fun _ _ => h_int.intervalIntegrable) a

variable [IsLocallyFiniteMeasure μ] {f : X → ℝ → E}
