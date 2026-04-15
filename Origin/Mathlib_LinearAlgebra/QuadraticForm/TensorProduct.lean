/-
Extracted from LinearAlgebra/QuadraticForm/TensorProduct.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The quadratic form on a tensor product

## Main definitions

* `QuadraticForm.tensorDistrib (Q₁ ⊗ₜ Q₂)`: the quadratic form on `M₁ ⊗ M₂` constructed by applying
  `Q₁` on `M₁` and `Q₂` on `M₂`. This construction is not available in characteristic two.

-/

universe uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

open LinearMap (BilinMap BilinForm)

open TensorProduct QuadraticMap

section CommRing

variable [CommRing R] [CommRing A]

variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]

variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]

variable [SMulCommClass R A M₁] [IsScalarTower R A M₁] [IsScalarTower R A N₁]

variable [Module R M₂] [Module R N₂]

section InvertibleTwo

variable [Invertible (2 : R)]

namespace QuadraticMap

variable (R A) in

def tensorDistrib :
    QuadraticMap A M₁ N₁ ⊗[R] QuadraticMap R M₂ N₂ →ₗ[A] QuadraticMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  -- while `letI`s would produce a better term than `let`, they would make this already-slow
  -- definition even slower.
  let toQ := BilinMap.toQuadraticMapLinearMap A A (M₁ ⊗[R] M₂)
  let tmulB := BilinMap.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
  let toB := AlgebraTensorModule.map
      (QuadraticMap.associated : QuadraticMap A M₁ N₁ →ₗ[A] BilinMap A M₁ N₁)
      (QuadraticMap.associated : QuadraticMap R M₂ N₂ →ₗ[R] BilinMap R M₂ N₂)
  toQ ∘ₗ tmulB ∘ₗ toB
