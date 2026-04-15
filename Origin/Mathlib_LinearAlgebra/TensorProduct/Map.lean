/-
Extracted from LinearAlgebra/TensorProduct/Map.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor products and linear maps

This file defines `TensorProduct.map`, the `R`-linear map from `M ⊗ N` to `M₂ ⊗ N₂` defined by
a pair of linear (or more generally semilinear) maps `f : M → M₂` and `g : N → N₂`.

The notation `f ⊗ₘ g` is available for this map.

We also define one-sided versions `lTensor` and `rTensor`.

## Tags

bilinear, tensor, tensor product
-/

section Semiring

variable {R R₂ R₃ R' R'' : Type*}

variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable {A M N P Q S : Type*}

variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]

variable [AddCommMonoid P'] [AddCommMonoid Q']

variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]

variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]

variable [DistribMulAction R' M]

variable [Module R'' M]

variable [Module R M] [Module R N] [Module R S]

variable [Module R P'] [Module R Q']

variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]

variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

variable [Module R P] [Module R Q]

variable {M N}

open LinearMap

def map (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) : M ⊗[R] N →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  lift <| comp (compl₂ (mk _ _ _) g) f
