/-
Extracted from Topology/MetricSpace/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Metric spaces

This file defines metric spaces and shows some of their basic properties.

Many definitions and theorems expected on metric spaces are already introduced on uniform spaces and
topological spaces. This includes open and closed sets, compactness, completeness, continuity
and uniform continuity.

## Main definitions

* `MetricSpace α`: A pseudometric space with the guarantee `dist x y = 0 → x = y`.
* `MetricSpace.ofDistTopology`: Construct a metric space from a compatible topology and distance.
* `MetricSpace.replaceUniformity`, `MetricSpace.replaceTopology`,
  `MetricSpace.replaceBornology`: Tools to construct a metric space on a type with a pre-existing
  uniformity, topology, or bornology in such a way that the definitional equalities for these
  structures are preserved; these are essential to avoid type class synthesis issues.

## Main results

* `dist_eq_zero`, `dist_pos`, `eq_of_forall_dist_le`, `eq_of_nndist_eq_zero`: core
  characterizations of equality via distance.

## Implementation notes
A lot of elementary properties don't require `eq_of_dist_eq_zero`, hence are stated and proven
for `PseudoMetricSpace`s in `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`.

## Tags

metric, pseudometric space, dist
-/

assert_not_exists Finset.sum

open Set Filter Bornology

open scoped NNReal Uniformity

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

variable [PseudoMetricSpace α]

class MetricSpace (α : Type u) : Type u extends PseudoMetricSpace α where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y
