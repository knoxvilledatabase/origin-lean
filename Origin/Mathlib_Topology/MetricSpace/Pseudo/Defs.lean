/-
Extracted from Topology/MetricSpace/Pseudo/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
## Pseudo-metric spaces

This file defines pseudo-metric spaces: these differ from metric spaces by not imposing the
condition `dist x y = 0 → x = y`.
Many definitions and theorems expected on (pseudo-)metric spaces are already introduced on uniform
spaces and topological spaces. For example: open and closed sets, compactness, completeness,
continuity and uniform continuity.

## Main definitions

* `Dist α`: Endows a space `α` with a function `dist a b`.
* `PseudoMetricSpace α`: A space endowed with a distance function, which can
  be zero even if the two elements are non-equal.
* `PseudoMetricSpace.ofDistTopology`: Construct a pseudometric space from a compatible topology
  and distance.
* `Metric.ball x ε`: The set of all points `y` with `dist y x < ε`.
* `Metric.closedBall x ε`: The set of all points `y` with `dist y x ≤ ε`.
* `Metric.sphere x ε`: The set of all points `y` with `dist y x = ε`.
* `nndist a b`: `dist` as a function to the non-negative reals.
* `Metric.Bounded s`: Whether a subset of a `PseudoMetricSpace` is bounded.
* `PseudoMetricSpace.replaceUniformity`, `PseudoMetricSpace.replaceTopology`,
  `PseudoMetricSpace.replaceBornology`: Tools to construct a pseudometric space on a type with a
  pre-existing uniformity, topology, or bornology in such a way that the definitional equalities
  for these structures are preserved; these are essential to avoid type class synthesis issues.
* `Real.pseudoMetricSpace`: The pseudometric space structure on `ℝ` with
  `dist x y = |x - y|`.
* `MetricSpace α`: A `PseudoMetricSpace` with the guarantee `dist x y = 0 → x = y`.

## Main results

* `PseudoMetricSpace.ext`: extensionality for pseudometric space structures.
* `dist_triangle`, `dist_nonneg`, `nndist_triangle`: core distance inequalities.
* `Metric.mk_uniformity_basis`, `Metric.mk_uniformity_basis_le`: tools for constructing bases for
  the uniformity, with `Metric.nhds_basis_ball` and `Metric.nhds_basis_closedBall` as basic
  neighborhood-basis corollaries.
* `Metric.tendsto_nhds_nhds`, `Metric.continuous_iff`: epsilon-delta characterizations of
  convergence and continuity.
* `Metric.mem_closure_iff`, `Metric.dense_iff`: characterizations of closure and dense sets.

## Tags

pseudometric space, dist
-/

assert_not_exists compactSpace_uniformity

open Set Filter TopologicalSpace Bornology

open scoped ENNReal NNReal Uniformity Topology

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

theorem UniformSpace.ofDist_aux (ε : ℝ) (hε : 0 < ε) : ∃ δ > (0 : ℝ), ∀ x < δ, ∀ y < δ, x + y < ε :=
  ⟨ε / 2, half_pos hε, fun _x hx _y hy => add_halves ε ▸ add_lt_add hx hy⟩
