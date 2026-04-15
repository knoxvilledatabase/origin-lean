/-
Extracted from Probability/Distributions/Geometric.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Geometric distributions over ℕ

Define the geometric measure over the natural numbers

## Main definitions
* `geometricPMFReal`: the function `p n ↦ (1-p) ^ n * p`
  for `n ∈ ℕ`, which is the probability density function of a geometric distribution with
  success probability `p ∈ (0,1]`.
* `geometricPMF`: `ℝ≥0∞`-valued pmf,
  `geometricPMF p = ENNReal.ofReal (geometricPMFReal p)`.
* `geometricMeasure`: a geometric measure on `ℕ`, parametrized by its success probability `p`.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

variable {p : ℝ}

section GeometricPMF

noncomputable

def geometricPMFReal (p : ℝ) (n : ℕ) : ℝ := (1 - p) ^ n * p

lemma geometricPMFRealSum (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    HasSum (fun n ↦ geometricPMFReal p n) 1 := by
  unfold geometricPMFReal
  have := hasSum_geometric_of_lt_one (sub_nonneg.mpr hp_le_one) (sub_lt_self 1 hp_pos)
  apply (hasSum_mul_right_iff (hp_pos.ne')).mpr at this
  simp only [sub_sub_cancel] at this
  rw [inv_mul_eq_div, div_self hp_pos.ne'] at this
  exact this

lemma geometricPMFReal_pos {n : ℕ} (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    0 < geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_pos.mpr hp_lt_one]

lemma geometricPMFReal_nonneg {n : ℕ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    0 ≤ geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_nonneg.mpr hp_le_one]

noncomputable

def geometricPMF (hp_pos : 0 < p) (hp_le_one : p ≤ 1) : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (geometricPMFReal p n), by
    apply ENNReal.hasSum_coe.mpr
    rw [← toNNReal_one]
    exact (geometricPMFRealSum hp_pos hp_le_one).toNNReal
      (fun n ↦ geometricPMFReal_nonneg hp_pos hp_le_one)⟩
