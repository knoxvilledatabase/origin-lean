/-
Extracted from Topology/MetricSpace/Congruence.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Congruences

This file defines `Congruent`, i.e., the equivalence between indexed families of points in a metric
space where all corresponding pairwise distances are the same. The motivating example are
triangles in the plane.

## Implementation notes

After considering two possible approaches to defining congruence — either based on equal pairwise
distances or the existence of an isometric equivalence — we have opted for the broader concept of
equal pairwise distances. This notion is commonly employed in the literature across various metric
spaces that lack an isometric equivalence.

For more details see the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry).

## Notation

* `v₁ ≅ v₂`: for `Congruent v₁ v₂`.
-/

variable {ι ι' : Type*} {P₁ P₂ P₃ P₄ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂]

variable [PseudoEMetricSpace P₃] [PseudoEMetricSpace P₄]

def Congruent (v₁ : ι → P₁) (v₂ : ι → P₂) : Prop :=
  ∀ i₁ i₂, edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂)
