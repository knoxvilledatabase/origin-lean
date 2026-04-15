/-
Extracted from Topology/UniformSpace/Ultra/Completion.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Completions of ultrametric (nonarchimedean) uniform spaces

## Main results

* `IsUltraUniformity.completion_iff`: a Hausdorff completion has a nonarchimedean uniformity
  iff the underlying space has a nonarchimedean uniformity.

-/

variable {X Y : Type*} [UniformSpace X] [UniformSpace Y]

open Filter Set Topology Uniformity

lemma IsUniformInducing.isUltraUniformity [IsUltraUniformity Y] {f : X → Y}
    (hf : IsUniformInducing f) : IsUltraUniformity X :=
  hf.comap_uniformSpace ▸ .comap inferInstance f

-- INSTANCE (free from Core): CauchyFilter.isSymm_gen
