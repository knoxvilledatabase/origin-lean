/-
Extracted from Topology/MetricSpace/Thickening.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Thickenings in pseudo-metric spaces

## Main definitions
* `Metric.thickening δ s`, the open thickening by radius `δ` of a set `s` in a pseudo emetric space.
* `Metric.cthickening δ s`, the closed thickening by radius `δ` of a set `s` in a pseudo emetric
  space.

## Main results
* `Disjoint.exists_thickenings`: two disjoint sets admit disjoint thickenings
* `Disjoint.exists_cthickenings`: two disjoint sets admit disjoint closed thickenings
* `IsCompact.exists_cthickening_subset_open`: if `s` is compact, `t` is open and `s ⊆ t`,
  some `cthickening` of `s` is contained in `t`.

* `Metric.hasBasis_nhdsSet_cthickening`: the `cthickening`s of a compact set `K` form a basis
  of the neighbourhoods of `K`
* `Metric.closure_eq_iInter_cthickening'`: the closure of a set equals the intersection
  of its closed thickenings of positive radii accumulating at zero.
  The same holds for open thickenings.
* `IsCompact.cthickening_eq_biUnion_closedBall`: if `s` is compact, `cthickening δ s` is the union
  of `closedBall`s of radius `δ` around `x : E`.

-/

noncomputable section

open NNReal ENNReal Topology Set Filter Bornology

universe u v w

variable {ι : Sort*} {α : Type u}

namespace Metric

section Thickening

variable [PseudoEMetricSpace α] {δ : ℝ} {s : Set α} {x : α}

def thickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEDist x E < ENNReal.ofReal δ }
