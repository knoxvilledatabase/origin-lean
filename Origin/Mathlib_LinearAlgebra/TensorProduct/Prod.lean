/-
Extracted from LinearAlgebra/TensorProduct/Prod.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Prod

noncomputable section

/-!
# Tensor products of products

This file shows that taking `TensorProduct`s commutes with taking `Prod`s in both arguments.

## Main results

* `TensorProduct.prodLeft`
* `TensorProduct.prodRight`

## Notes

See `Mathlib.LinearAlgebra.TensorProduct.Pi` for arbitrary products.

-/

universe uR uM₁ uM₂ uM₃

variable (R : Type uR) (M₁ : Type uM₁) (M₂ : Type uM₂) (M₃ : Type uM₃)

namespace TensorProduct

variable [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M₁] [Module R M₂] [Module R M₃]

attribute [ext] TensorProduct.ext

def prodRight : M₁ ⊗[R] (M₂ × M₃) ≃ₗ[R] ((M₁ ⊗[R] M₂) × (M₁ ⊗[R] M₃)) :=
  LinearEquiv.ofLinear
    (lift <|
      LinearMap.prodMapLinear R M₂ M₃ (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₃) R
        ∘ₗ LinearMap.prod (mk _ _ _) (mk _ _ _))
    (LinearMap.coprod
      (LinearMap.lTensor _ <| LinearMap.inl _ _ _)
      (LinearMap.lTensor _ <| LinearMap.inr _ _ _))
    (by ext <;> simp)
    (by ext <;> simp)

@[simp] theorem prodRight_symm_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    (prodRight R M₁ M₂ M₃).symm (m₁ ⊗ₜ m₂, m₁ ⊗ₜ m₃) = (m₁ ⊗ₜ (m₂, m₃)) :=
  (LinearEquiv.symm_apply_eq _).mpr rfl

def prodLeft : (M₁ × M₂) ⊗[R] M₃ ≃ₗ[R] ((M₁ ⊗[R] M₃) × (M₂ ⊗[R] M₃)) :=
  TensorProduct.comm _ _ _
    ≪≫ₗ TensorProduct.prodRight R _ _ _
    ≪≫ₗ (TensorProduct.comm R _ _).prod (TensorProduct.comm R _ _)

@[simp] theorem prodLeft_symm_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    (prodLeft R M₁ M₂ M₃).symm (m₁ ⊗ₜ m₃, m₂ ⊗ₜ m₃) = ((m₁, m₂) ⊗ₜ m₃) :=
  (LinearEquiv.symm_apply_eq _).mpr rfl

end TensorProduct
