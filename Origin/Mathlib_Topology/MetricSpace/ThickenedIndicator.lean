/-
Extracted from Topology/MetricSpace/ThickenedIndicator.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Thickened indicators

This file is about thickened indicators of sets in (pseudo e)metric spaces. For a decreasing
sequence of thickening radii tending to 0, the thickened indicators of a closed set form a
decreasing pointwise converging approximation of the indicator function of the set, where the
members of the approximating sequence are nonnegative bounded continuous functions.

## Main definitions

* `thickenedIndicatorAux δ E`: The `δ`-thickened indicator of a set `E` as an
  unbundled `ℝ≥0∞`-valued function.
* `thickenedIndicator δ E`: The `δ`-thickened indicator of a set `E` as a bundled
  bounded continuous `ℝ≥0`-valued function.

## Main results

* For a sequence of thickening radii tending to 0, the `δ`-thickened indicators of a set `E` tend
  pointwise to the indicator of `closure E`.
  - `thickenedIndicatorAux_tendsto_indicator_closure`: The version is for the
    unbundled `ℝ≥0∞`-valued functions.
  - `thickenedIndicator_tendsto_indicator_closure`: The version is for the bundled `ℝ≥0`-valued
    bounded continuous functions.

-/

open NNReal ENNReal Topology BoundedContinuousFunction Set Metric Filter

noncomputable section thickenedIndicator

variable {α : Type*} [PseudoEMetricSpace α]

def thickenedIndicatorAux (δ : ℝ) (E : Set α) : α → ℝ≥0∞ :=
  fun x : α => (1 : ℝ≥0∞) - infEDist x E / ENNReal.ofReal δ

theorem continuous_thickenedIndicatorAux {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    Continuous (thickenedIndicatorAux δ E) := by
  unfold thickenedIndicatorAux
  let f := fun x : α => (⟨1, infEDist x E / ENNReal.ofReal δ⟩ : ℝ≥0 × ℝ≥0∞)
  let sub := fun p : ℝ≥0 × ℝ≥0∞ => (p.1 : ℝ≥0∞) - p.2
  rw [show (fun x : α => (1 : ℝ≥0∞) - infEDist x E / ENNReal.ofReal δ) = sub ∘ f by rfl]
  apply (@ENNReal.continuous_nnreal_sub 1).comp
  apply (ENNReal.continuous_div_const (ENNReal.ofReal δ) _).comp continuous_infEDist
  norm_num [δ_pos]

theorem thickenedIndicatorAux_le_one (δ : ℝ) (E : Set α) (x : α) :
    thickenedIndicatorAux δ E x ≤ 1 := by
  apply tsub_le_self (α := ℝ≥0∞)
