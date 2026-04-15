/-
Extracted from LinearAlgebra/BilinearForm/TensorProduct.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The bilinear form on a tensor product

## Main definitions

* `LinearMap.BilinMap.tensorDistrib (B₁ ⊗ₜ B₂)`: the bilinear form on `M₁ ⊗ M₂` constructed by
  applying `B₁` on `M₁` and `B₂` on `M₂`.
* `LinearMap.BilinMap.tensorDistribEquiv`: `BilinForm.tensorDistrib` as an equivalence on finite
  free modules.

-/

universe u v w uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

open TensorProduct

namespace LinearMap

open LinearMap (BilinMap BilinForm)

section CommSemiring

variable [CommSemiring R] [CommSemiring A]

variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]

variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]

variable [SMulCommClass R A M₁] [IsScalarTower R A M₁]

variable [SMulCommClass R A N₁] [IsScalarTower R A N₁]

variable [Module R M₂] [Module R N₂]

namespace BilinMap

variable (R A) in

def tensorDistrib :
    (BilinMap A M₁ N₁ ⊗[R] BilinMap R M₂ N₂) →ₗ[A] BilinMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  (TensorProduct.lift.equiv (.id A) (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂)).symm.toLinearMap ∘ₗ
  ((LinearMap.llcomp A _ _ _).flip
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A M₁ M₂ M₁ M₂).toLinearMap)
  ∘ₗ TensorProduct.AlgebraTensorModule.homTensorHomMap R _ _ _ _ _ _
  ∘ₗ (TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.lift.equiv (.id A) M₁ M₁ N₁)
    (TensorProduct.lift.equiv (.id R) _ _ _)).toLinearMap
