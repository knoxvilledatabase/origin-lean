/-
Extracted from Topology/MetricSpace/Antilipschitz.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Antilipschitz functions

We say that a map `f : α → β` between two (extended) metric spaces is
`AntilipschitzWith K`, `K ≥ 0`, if for all `x, y` we have `edist x y ≤ K * edist (f x) (f y)`.
For a metric space, the latter inequality is equivalent to `dist x y ≤ K * dist (f x) (f y)`.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. We do not require `0 < K` in the definition, mostly because
we do not have a `posreal` type.
-/

open Bornology Filter Set Topology

open scoped NNReal ENNReal Uniformity

variable {α β γ : Type*}

def AntilipschitzWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β) :=
  ∀ x y, edist x y ≤ K * edist (f x) (f y)

protected lemma AntilipschitzWith.edist_lt_top [PseudoEMetricSpace α] [PseudoMetricSpace β]
    {K : ℝ≥0} {f : α → β} (h : AntilipschitzWith K f) (x y : α) : edist x y < ⊤ :=
  (h x y).trans_lt <| ENNReal.mul_lt_top ENNReal.coe_lt_top (edist_lt_top _ _)

theorem AntilipschitzWith.edist_ne_top [PseudoEMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} (h : AntilipschitzWith K f) (x y : α) : edist x y ≠ ⊤ :=
  (h.edist_lt_top x y).ne

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0} {f : α → β}

theorem antilipschitzWith_iff_le_mul_nndist :
    AntilipschitzWith K f ↔ ∀ x y, nndist x y ≤ K * nndist (f x) (f y) := by
  simp only [AntilipschitzWith, edist_nndist]
  norm_cast

alias ⟨AntilipschitzWith.le_mul_nndist, AntilipschitzWith.of_le_mul_nndist⟩ :=

  antilipschitzWith_iff_le_mul_nndist

theorem antilipschitzWith_iff_le_mul_dist :
    AntilipschitzWith K f ↔ ∀ x y, dist x y ≤ K * dist (f x) (f y) := by
  simp only [antilipschitzWith_iff_le_mul_nndist, dist_nndist]
  norm_cast

alias ⟨AntilipschitzWith.le_mul_dist, AntilipschitzWith.of_le_mul_dist⟩ :=

  antilipschitzWith_iff_le_mul_dist

namespace AntilipschitzWith

theorem mul_le_nndist (hf : AntilipschitzWith K f) (x y : α) :
    K⁻¹ * nndist x y ≤ nndist (f x) (f y) := by
  simpa only [div_eq_inv_mul] using NNReal.div_le_of_le_mul' (hf.le_mul_nndist x y)

theorem mul_le_dist (hf : AntilipschitzWith K f) (x y : α) :
    (K⁻¹ * dist x y : ℝ) ≤ dist (f x) (f y) := mod_cast hf.mul_le_nndist x y

end AntilipschitzWith

end Metric

namespace AntilipschitzWith

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

variable {K : ℝ≥0} {f : α → β}

open Metric
