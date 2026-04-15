/-
Extracted from Topology/MetricSpace/HausdorffDistance.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Hausdorff distance

The Hausdorff distance on subsets of a metric (or emetric) space.

Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point of `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.

## Main definitions

This file introduces:
* `Metric.infEDist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `Metric.hausdorffEDist s t`, the Hausdorff edistance of two sets in an emetric space
* Versions of these notions on metric spaces, called respectively `Metric.infDist`
  and `Metric.hausdorffDist`

## Main results
* `infEDist_closure`: the edistance to a set and its closure coincide
* `Metric.mem_closure_iff_infEDist_zero`: a point `x` belongs to the closure of `s` iff
  `infEDist x s = 0`
* `IsCompact.exists_infEDist_eq_edist`: if `s` is compact and non-empty, there exists a point `y`
  which attains this edistance
* `IsOpen.exists_iUnion_isClosed`: every open set `U` can be written as the increasing union
  of countably many closed subsets of `U`

* `hausdorffEDist_closure`: replacing a set by its closure does not change the Hausdorff edistance
* `hausdorffEDist_zero_iff_closure_eq_closure`: two sets have Hausdorff edistance zero
  iff their closures coincide
* the Hausdorff edistance is symmetric and satisfies the triangle inequality
* in particular, closed sets in an emetric space are an emetric space
  (this is shown in `EMetricSpace.Closeds.emetricSpace`)

* versions of these notions on metric spaces
* `hausdorffEDist_ne_top_of_nonempty_of_bounded`: if two sets in a metric space
  are nonempty and bounded in a metric space, they are at finite Hausdorff edistance.

## Tags
metric space, Hausdorff distance
-/

noncomputable section

open NNReal ENNReal Topology Set Filter Pointwise Bornology

universe u v w

variable {ι : Sort*} {α : Type u} {β : Type v}

namespace Metric

section InfEDist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t : Set α} {Φ : α → β}

/-! ### Distance of a point to a set as a function into `ℝ≥0∞`. -/

def infEDist (x : α) (s : Set α) : ℝ≥0∞ :=
  ⨅ y ∈ s, edist x y
