/-
Extracted from MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

noncomputable section

/-!
# Chebyshev-Markov inequality in terms of Lp seminorms

In this file we formulate several versions of the Chebyshev-Markov inequality
in terms of the `MeasureTheory.eLpNorm` seminorm.
-/

open scoped NNReal ENNReal

namespace MeasureTheory

variable {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} (μ : Measure α) {f : α → E}

theorem pow_mul_meas_ge_le_eLpNorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    (ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal }) ^ (1 / p.toReal) ≤ eLpNorm f p μ := by
  rw [eLpNorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top]
  gcongr
  exact mul_meas_ge_le_lintegral₀ (hf.ennnorm.pow_const _) ε

alias pow_mul_meas_ge_le_snorm := pow_mul_meas_ge_le_eLpNorm

theorem mul_meas_ge_le_pow_eLpNorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal } ≤ eLpNorm f p μ ^ p.toReal := by
  have : 1 / p.toReal * p.toReal = 1 := by
    refine one_div_mul_cancel ?_
    rw [Ne, ENNReal.toReal_eq_zero_iff]
    exact not_or_intro hp_ne_zero hp_ne_top
  rw [← ENNReal.rpow_one (ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal }), ← this, ENNReal.rpow_mul]
  gcongr
  exact pow_mul_meas_ge_le_eLpNorm μ hp_ne_zero hp_ne_top hf ε

alias mul_meas_ge_le_pow_snorm := mul_meas_ge_le_pow_eLpNorm

theorem mul_meas_ge_le_pow_eLpNorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε ^ p.toReal * μ { x | ε ≤ ‖f x‖₊ } ≤ eLpNorm f p μ ^ p.toReal := by
  convert mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top hf (ε ^ p.toReal) using 4
  ext x
  rw [ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]

alias mul_meas_ge_le_pow_snorm' := mul_meas_ge_le_pow_eLpNorm'

theorem meas_ge_le_mul_pow_eLpNorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖₊ } ≤ ε⁻¹ ^ p.toReal * eLpNorm f p μ ^ p.toReal := by
  by_cases h : ε = ∞
  · simp [h]
  have hεpow : ε ^ p.toReal ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε) h).ne.symm
  have hεpow' : ε ^ p.toReal ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg h
  rw [ENNReal.inv_rpow, ← ENNReal.mul_le_mul_left hεpow hεpow', ← mul_assoc,
    ENNReal.mul_inv_cancel hεpow hεpow', one_mul]
  exact mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top hf ε

alias meas_ge_le_mul_pow_snorm := meas_ge_le_mul_pow_eLpNorm

theorem Memℒp.meas_ge_lt_top' {μ : Measure α} (hℒp : Memℒp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖₊ } < ∞ := by
  apply (meas_ge_le_mul_pow_eLpNorm μ hp_ne_zero hp_ne_top hℒp.aestronglyMeasurable hε).trans_lt
    (ENNReal.mul_lt_top ?_ ?_)
  · simp [hε, lt_top_iff_ne_top]
  · simp [hℒp.eLpNorm_lt_top.ne, lt_top_iff_ne_top]

theorem Memℒp.meas_ge_lt_top {μ : Measure α} (hℒp : Memℒp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) {ε : ℝ≥0} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖₊ } < ∞ := by
  simp_rw [← ENNReal.coe_le_coe]
  apply hℒp.meas_ge_lt_top' hp_ne_zero hp_ne_top (by simp [hε])

end MeasureTheory
