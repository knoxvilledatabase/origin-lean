/-
Extracted from Topology/MetricSpace/Similarity.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Similarities

This file defines `Similar`, i.e., the equivalence between indexed sets of points in a metric space
where all corresponding pairwise distances have the same ratio. The motivating example is
triangles in the plane.

## Implementation notes

For more details see the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry).

## Notation
Let `P₁` and `P₂` be metric spaces, let `ι` be an index set, and let `v₁ : ι → P₁` and
`v₂ : ι → P₂` be indexed families of points.

* `(v₁ ∼ v₂ : Prop)` represents that `(v₁ : ι → P₁)` and `(v₂ : ι → P₂)` are similar.
-/

open scoped NNReal

variable {ι ι' : Type*} {P₁ P₂ P₃ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] [PseudoEMetricSpace P₃]

def Similar (v₁ : ι → P₁) (v₂ : ι → P₂) : Prop :=
  ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂))
