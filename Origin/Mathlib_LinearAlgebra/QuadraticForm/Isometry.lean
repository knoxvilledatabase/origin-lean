/-
Extracted from LinearAlgebra/QuadraticForm/Isometry.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isometric linear maps

## Main definitions

* `QuadraticMap.Isometry`: `LinearMap`s which map between two different quadratic forms

## Notation

`Q₁ →qᵢ Q₂` is notation for `Q₁.Isometry Q₂`.
-/

variable {R M M₁ M₂ M₃ M₄ N : Type*}

namespace QuadraticMap

variable [CommSemiring R]

variable [AddCommMonoid M]

variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]

variable [AddCommMonoid N]

variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R N]

structure Isometry (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N) extends M₁ →ₗ[R] M₂ where
  /-- The quadratic form agrees across the map. -/
  map_app' : ∀ m, Q₂ (toFun m) = Q₁ m

namespace Isometry
