/-
Extracted from Analysis/SpecialFunctions/JapaneseBracket.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Japanese Bracket

In this file, we show that Japanese bracket $(1 + \|x\|^2)^{1/2}$ can be estimated from above
and below by $1 + \|x\|$.
The functions $(1 + \|x\|^2)^{-r/2}$ and $(1 + |x|)^{-r}$ are integrable provided that `r` is larger
than the dimension.

## Main statements

* `integrable_one_add_norm`: the function $(1 + |x|)^{-r}$ is integrable
* `integrable_jap` the Japanese bracket is integrable

-/

noncomputable section

open scoped NNReal Filter Topology ENNReal

open Asymptotics Filter Set Real MeasureTheory Module

variable {E : Type*} [NormedAddCommGroup E]

theorem sqrt_one_add_norm_sq_le (x : E) : √((1 : ℝ) + ‖x‖ ^ 2) ≤ 1 + ‖x‖ := by
  rw [sqrt_le_left (by positivity)]
  simp [add_sq]

theorem one_add_norm_le_sqrt_two_mul_sqrt (x : E) :
    (1 : ℝ) + ‖x‖ ≤ √2 * √(1 + ‖x‖ ^ 2) := by
  rw [← sqrt_mul zero_le_two]
  have := sq_nonneg (‖x‖ - 1)
  apply le_sqrt_of_sq_le
  linarith

theorem rpow_neg_one_add_norm_sq_le {r : ℝ} (x : E) (hr : 0 < r) :
    ((1 : ℝ) + ‖x‖ ^ 2) ^ (-r / 2) ≤ (2 : ℝ) ^ (r / 2) * (1 + ‖x‖) ^ (-r) :=
  calc
    ((1 : ℝ) + ‖x‖ ^ 2) ^ (-r / 2)
      = (2 : ℝ) ^ (r / 2) * ((√2 * √((1 : ℝ) + ‖x‖ ^ 2)) ^ r)⁻¹ := by
      rw [rpow_div_two_eq_sqrt, rpow_div_two_eq_sqrt, mul_rpow, mul_inv, rpow_neg,
        mul_inv_cancel_left₀] <;> positivity
    _ ≤ (2 : ℝ) ^ (r / 2) * ((1 + ‖x‖) ^ r)⁻¹ := by
      gcongr
      apply one_add_norm_le_sqrt_two_mul_sqrt
    _ = (2 : ℝ) ^ (r / 2) * (1 + ‖x‖) ^ (-r) := by rw [rpow_neg]; positivity

theorem le_rpow_one_add_norm_iff_norm_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : E) :
    t ≤ (1 + ‖x‖) ^ (-r) ↔ ‖x‖ ≤ t ^ (-r⁻¹) - 1 := by
  rw [le_sub_iff_add_le', neg_inv]
  exact (Real.le_rpow_inv_iff_of_neg (by positivity) ht (neg_lt_zero.mpr hr)).symm

variable (E)

theorem closedBall_rpow_sub_one_eq_empty_aux {r t : ℝ} (hr : 0 < r) (ht : 1 < t) :
    Metric.closedBall (0 : E) (t ^ (-r⁻¹) - 1) = ∅ := by
  rw [Metric.closedBall_eq_empty, sub_neg]
  exact Real.rpow_lt_one_of_one_lt_of_neg ht (by simp only [hr, Right.neg_neg_iff, inv_pos])

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {E}

theorem finite_integral_rpow_sub_one_pow_aux {r : ℝ} (n : ℕ) (hnr : (n : ℝ) < r) :
    (∫⁻ x : ℝ in Ioc 0 1, ENNReal.ofReal ((x ^ (-r⁻¹) - 1) ^ n)) < ∞ := by
  have hr : 0 < r := lt_of_le_of_lt n.cast_nonneg hnr
  have h_int x (hx : x ∈ Ioc (0 : ℝ) 1) := by
    calc
      ENNReal.ofReal ((x ^ (-r⁻¹) - 1) ^ n) ≤ .ofReal ((x ^ (-r⁻¹) - 0) ^ n) := by
        gcongr
        · rw [sub_nonneg]
          exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx.1 hx.2 (by simpa using hr.le)
        · simp
      _ = .ofReal (x ^ (-(r⁻¹ * n))) := by simp [rpow_mul hx.1.le, ← neg_mul]
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc h_int) ?_
  refine IntegrableOn.setLIntegral_lt_top ?_
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  apply intervalIntegral.intervalIntegrable_rpow'
  rwa [neg_lt_neg_iff, inv_mul_lt_iff₀' hr, one_mul]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem finite_integral_one_add_norm {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
    (∫⁻ x : E, ENNReal.ofReal ((1 + ‖x‖) ^ (-r)) ∂μ) < ∞ := by
  have hr : 0 < r := lt_of_le_of_lt (finrank ℝ E).cast_nonneg hnr
  -- We start by applying the layer cake formula
  have h_meas : Measurable fun ω : E => (1 + ‖ω‖) ^ (-r) := by fun_prop
  have h_pos : ∀ x : E, 0 ≤ (1 + ‖x‖) ^ (-r) := fun x ↦ by positivity
  rw [lintegral_eq_lintegral_meas_le μ (Eventually.of_forall h_pos) h_meas.aemeasurable]
  have h_int : ∀ t, 0 < t → μ {a : E | t ≤ (1 + ‖a‖) ^ (-r)} =
      μ (Metric.closedBall (0 : E) (t ^ (-r⁻¹) - 1)) := fun t ht ↦ by
    congr 1
    ext x
    simp only [mem_setOf_eq, mem_closedBall_zero_iff]
    exact le_rpow_one_add_norm_iff_norm_le hr (mem_Ioi.mp ht) x
  rw [setLIntegral_congr_fun measurableSet_Ioi h_int]
  set f := fun t : ℝ ↦ μ (Metric.closedBall (0 : E) (t ^ (-r⁻¹) - 1))
  set mB := μ (Metric.ball (0 : E) 1)
  -- the next two inequalities are in fact equalities but we don't need that
  calc
    ∫⁻ t in Ioi 0, f t ≤ ∫⁻ t in Ioc 0 1 ∪ Ioi 1, f t := lintegral_mono_set Ioi_subset_Ioc_union_Ioi
    _ ≤ (∫⁻ t in Ioc 0 1, f t) + ∫⁻ t in Ioi 1, f t := lintegral_union_le _ _ _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · -- We use estimates from auxiliary lemmas to deal with integral from `0` to `1`
    have h_int' : ∀ t ∈ Ioc (0 : ℝ) 1,
        f t = ENNReal.ofReal ((t ^ (-r⁻¹) - 1) ^ finrank ℝ E) * mB := fun t ht ↦ by
      refine μ.addHaar_closedBall (0 : E) ?_
      rw [sub_nonneg]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 (by simp [hr.le])
    rw [setLIntegral_congr_fun measurableSet_Ioc h_int',
      lintegral_mul_const' _ _ measure_ball_lt_top.ne]
    exact ENNReal.mul_lt_top
      (finite_integral_rpow_sub_one_pow_aux (finrank ℝ E) hnr) measure_ball_lt_top
  · -- The integral from 1 to ∞ is zero:
    have h_int'' : ∀ t ∈ Ioi (1 : ℝ), f t = 0 := fun t ht => by
      simp only [f, closedBall_rpow_sub_one_eq_empty_aux E hr ht, measure_empty]
    -- The integral over the constant zero function is finite:
    rw [setLIntegral_congr_fun measurableSet_Ioi h_int'', lintegral_const 0,
      zero_mul]
    exact WithTop.top_pos

theorem integrable_one_add_norm {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
    Integrable (fun x ↦ (1 + ‖x‖) ^ (-r)) μ := by
  constructor
  · apply Measurable.aestronglyMeasurable (by fun_prop)
  -- Lower Lebesgue integral
  have : (∫⁻ a : E, ‖(1 + ‖a‖) ^ (-r)‖ₑ ∂μ) = ∫⁻ a : E, ENNReal.ofReal ((1 + ‖a‖) ^ (-r)) ∂μ :=
    lintegral_enorm_of_nonneg fun _ => rpow_nonneg (by positivity) _
  rw [hasFiniteIntegral_iff_enorm, this]
  exact finite_integral_one_add_norm hnr

theorem integrable_rpow_neg_one_add_norm_sq {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
    Integrable (fun x ↦ ((1 : ℝ) + ‖x‖ ^ 2) ^ (-r / 2)) μ := by
  have hr : 0 < r := lt_of_le_of_lt (finrank ℝ E).cast_nonneg hnr
  refine ((integrable_one_add_norm hnr).const_mul <| (2 : ℝ) ^ (r / 2)).mono'
    ?_ (Eventually.of_forall fun x => ?_)
  · apply Measurable.aestronglyMeasurable (by fun_prop)
  refine (abs_of_pos ?_).trans_le (rpow_neg_one_add_norm_sq_le x hr)
  positivity
