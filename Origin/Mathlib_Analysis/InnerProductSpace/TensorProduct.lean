/-
Extracted from Analysis/InnerProductSpace/TensorProduct.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Inner product space structure on tensor product spaces

This file provides the inner product space structure on tensor product spaces.

We define the inner product on `E ⊗ F` by `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`, when `E` and `F` are
inner product spaces.

## Main definitions:

* `TensorProduct.instNormedAddCommGroup`: the normed additive group structure on tensor products,
  where `‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`.
* `TensorProduct.instInnerProductSpace`: the inner product space structure on tensor products, where
  `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`.
* `TensorProduct.mapIsometry`: the linear isometry version of `TensorProduct.map f g` when
  `f` and `g` are linear isometries.
* `TensorProduct.congrIsometry`: the linear isometry equivalence version of
  `TensorProduct.congr f g` when `f` and `g` are linear isometry equivalences.
* `TensorProduct.mapInclIsometry`: the linear isometry version of `TensorProduct.mapIncl`.
* `TensorProduct.commIsometry`: the linear isometry version of `TensorProduct.comm`.
* `TensorProduct.lidIsometry`: the linear isometry version of `TensorProduct.lid`.
* `TensorProduct.assocIsometry`: the linear isometry version of `TensorProduct.assoc`.
* `OrthonormalBasis.tensorProduct`: the orthonormal basis of the tensor product of two orthonormal
  bases.

## TODO:

* Define the continuous linear map version of `TensorProduct.map`.
* Complete space of tensor products.
* Define the normed space without needing inner products, this should be analogous to
  `Mathlib/Analysis/NormedSpace/PiTensorProduct/InjectiveSeminorm.lean`.

-/

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open scoped TensorProduct

namespace TensorProduct

set_option backward.privateInPublic true in

private abbrev inner_ : E ⊗[𝕜] F →ₗ⋆[𝕜] E ⊗[𝕜] F →ₗ[𝕜] 𝕜 :=
  (lift <| mapBilinear (.id 𝕜) E F 𝕜 𝕜).compr₂ (LinearMap.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): instInner

variable (𝕜) in
