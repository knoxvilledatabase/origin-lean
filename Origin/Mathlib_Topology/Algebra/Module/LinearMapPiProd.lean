/-
Extracted from Topology/Algebra/Module/LinearMapPiProd.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous linear maps on products and Pi types
-/

assert_not_exists TrivialStar

open LinearMap (ker range)

open Topology Filter Pointwise

universe u v w u'

namespace ContinuousLinearMap

section Semiring

/-!
### Properties that hold for non-necessarily commutative semirings.
-/

variable
  {R : Type*} [Semiring R]
  {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R M₄]

protected def prod (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) :
    M₁ →L[R] M₂ × M₃ :=
  ⟨(f₁ : M₁ →ₗ[R] M₂).prod f₂, f₁.2.prodMk f₂.2⟩
