/-
Extracted from Topology/MetricSpace/Lipschitz.lean
Genuine: 13 of 15 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.
Finally, `f : α → β` is called *locally Lipschitz continuous* if each `x : α` has a neighbourhood
on which `f` is Lipschitz continuous (with some constant).

In this file we specialize various facts about Lipschitz continuous maps
to the case of (pseudo) metric spaces.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `LipschitzWith (Real.toNNReal K) f`.
-/

assert_not_exists Module.Basis Ideal ContinuousMul

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

theorem lipschitzWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} : LipschitzWith K f ↔ ∀ x y, dist (f x) (f y) ≤ K * dist x y := by
  simp only [LipschitzWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzWith.dist_le_mul, LipschitzWith.of_dist_le_mul⟩ := lipschitzWith_iff_dist_le_mul

theorem lipschitzOnWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {s : Set α} {f : α → β} :
    LipschitzOnWith K f s ↔ ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y := by
  simp only [LipschitzOnWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzOnWith.dist_le_mul, LipschitzOnWith.of_dist_le_mul⟩ :=

  lipschitzOnWith_iff_dist_le_mul

namespace LipschitzWith

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ] {K : ℝ≥0} {f : α → β}
  {x y : α} {r : ℝ}

protected theorem of_dist_le' {K : ℝ} (h : ∀ x y, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith (Real.toNNReal K) f :=
  of_dist_le_mul fun x y =>
    le_trans (h x y) <| by gcongr; apply Real.le_coe_toNNReal

protected theorem mk_one (h : ∀ x y, dist (f x) (f y) ≤ dist x y) : LipschitzWith 1 f :=
  of_dist_le_mul <| by simpa only [NNReal.coe_one, one_mul] using h

protected theorem of_le_add_mul' {f : α → ℝ} (K : ℝ) (h : ∀ x y, f x ≤ f y + K * dist x y) :
    LipschitzWith (Real.toNNReal K) f :=
  have I : ∀ x y, f x - f y ≤ K * dist x y := fun x y => sub_le_iff_le_add'.2 (h x y)
  LipschitzWith.of_dist_le' fun x y => abs_sub_le_iff.2 ⟨I x y, dist_comm y x ▸ I y x⟩

protected theorem of_le_add_mul {f : α → ℝ} (K : ℝ≥0) (h : ∀ x y, f x ≤ f y + K * dist x y) :
    LipschitzWith K f := by simpa only [Real.toNNReal_coe] using LipschitzWith.of_le_add_mul' K h

protected theorem of_le_add {f : α → ℝ} (h : ∀ x y, f x ≤ f y + dist x y) : LipschitzWith 1 f :=
  LipschitzWith.of_le_add_mul 1 <| by simpa only [NNReal.coe_one, one_mul]

protected theorem le_add_mul {f : α → ℝ} {K : ℝ≥0} (h : LipschitzWith K f) (x y) :
    f x ≤ f y + K * dist x y :=
  sub_le_iff_le_add'.1 <| le_trans (le_abs_self _) <| h.dist_le_mul x y

protected theorem iff_le_add_mul {f : α → ℝ} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ x y, f x ≤ f y + K * dist x y :=
  ⟨LipschitzWith.le_add_mul, LipschitzWith.of_le_add_mul K⟩

theorem nndist_le (hf : LipschitzWith K f) (x y : α) : nndist (f x) (f y) ≤ K * nndist x y :=
  hf.dist_le_mul x y

theorem dist_le_mul_of_le (hf : LipschitzWith K f) (hr : dist x y ≤ r) : dist (f x) (f y) ≤ K * r :=
  (hf.dist_le_mul x y).trans <| by gcongr

theorem mapsTo_closedBall (hf : LipschitzWith K f) (x : α) (r : ℝ) :
    MapsTo f (Metric.closedBall x r) (Metric.closedBall (f x) (K * r)) := fun _y hy =>
  hf.dist_le_mul_of_le hy

-- DISSOLVED: dist_lt_mul_of_lt

-- DISSOLVED: mapsTo_ball

def toLocallyBoundedMap (f : α → β) (hf : LipschitzWith K f) : LocallyBoundedMap α β :=
  LocallyBoundedMap.ofMapBounded f fun _s hs =>
    let ⟨C, hC⟩ := Metric.isBounded_iff.1 hs
    Metric.isBounded_iff.2 ⟨K * C, forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy =>
      hf.dist_le_mul_of_le (hC hx hy)⟩
