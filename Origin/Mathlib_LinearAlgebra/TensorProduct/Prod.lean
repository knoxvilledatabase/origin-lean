/-
Extracted from LinearAlgebra/TensorProduct/Prod.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor products of products

This file shows that taking `TensorProduct`s commutes with taking `Prod`s in both arguments.

## Main results

* `TensorProduct.prodLeft`
* `TensorProduct.prodRight`

## Notes

See `Mathlib/LinearAlgebra/TensorProduct/Pi.lean` for arbitrary products.

-/

variable (R S M₁ M₂ M₃ : Type*)

namespace TensorProduct

variable [CommSemiring R] [Semiring S] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Algebra R S]

variable [Module R M₁] [Module S M₁] [IsScalarTower R S M₁] [Module R M₂] [Module R M₃]

attribute [ext] TensorProduct.ext

def prodRight : M₁ ⊗[R] (M₂ × M₃) ≃ₗ[S] (M₁ ⊗[R] M₂) × (M₁ ⊗[R] M₃) :=
  LinearEquiv.ofLinear
    (TensorProduct.AlgebraTensorModule.lift <|
      LinearMap.prodMapLinear R M₂ M₃ (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₃) S ∘ₗ
        LinearMap.prod (AlgebraTensorModule.mk R S M₁ M₂) (AlgebraTensorModule.mk R S M₁ M₃))
    (LinearMap.coprod
      (AlgebraTensorModule.lTensor _ _ <| LinearMap.inl _ _ _)
      (AlgebraTensorModule.lTensor _ _ <| LinearMap.inr _ _ _))
    (by ext <;> simp)
    (by ext <;> simp)
