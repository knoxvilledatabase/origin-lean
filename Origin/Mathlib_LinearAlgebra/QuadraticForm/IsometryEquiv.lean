/-
Extracted from LinearAlgebra/QuadraticForm/IsometryEquiv.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Isometric equivalences with respect to quadratic forms

## Main definitions

* `QuadraticForm.IsometryEquiv`: `LinearEquiv`s which map between two different quadratic forms
* `QuadraticForm.Equivalent`: propositional version of the above

## Main results

* `equivalent_weighted_sum_squares`: in finite dimensions, any quadratic form is equivalent to a
  parametrization of `QuadraticForm.weightedSumSquares`.
-/

open Module QuadraticMap

variable {ι R K M M₁ M₂ M₃ V N : Type*}

namespace QuadraticMap

variable [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
         [AddCommMonoid N]

variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R N]

structure IsometryEquiv (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
    extends M₁ ≃ₗ[R] M₂ where
  map_app' : ∀ m, Q₂ (toFun m) = Q₁ m

def Equivalent (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N) : Prop :=
  Nonempty (Q₁.IsometryEquiv Q₂)

namespace IsometryEquiv

variable {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} {Q₃ : QuadraticMap R M₃ N}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
