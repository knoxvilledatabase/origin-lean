/-
Extracted from Topology/MetricSpace/MetricSeparated.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Metric separation

This file defines a few notions of separations of sets in a metric space.


The first notion (`Metric.IsSeparated`) is quantitative and describes a single set: a set `s` is
`ε`-separated if the distance between any two distinct elements is strictly greater than `ε`

The second notion (`Metric.AreSeparated`) is qualitative and about two sets: Two sets `s` and `t`
are separated if the distance between `x ∈ s` and `y ∈ t` is bounded from below by a positive
constant.
-/

open EMetric Set

open scoped NNReal ENNReal

noncomputable section

namespace Metric

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

variable {s t : Set X} {ε δ : ℝ≥0∞} {x : X} {y : Y}

/-!
### Metric-separated sets

In this section we define the predicate `Metric.IsSeparated` for `ε`-separated sets.
-/

def IsSeparated (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε < edist · ·)

lemma isSeparated_iff_setRelIsSeparated :
    IsSeparated ε s ↔ SetRel.IsSeparated {(x, y) | edist x y ≤ ε} s := by
  simp [IsSeparated, SetRel.IsSeparated]
