/-
Extracted from RingTheory/PolynomialAlgebra.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Base change of polynomial algebras

Given `[CommSemiring R] [Semiring A] [Algebra R A]` we show `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
-/

assert_not_exists Matrix

universe u v w

open Polynomial TensorProduct

open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R S A : Type*)

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Algebra R S] [Algebra S A] [IsScalarTower R S A]

namespace PolyEquivTensor

def toFunBilinear : A →ₗ[A] R[X] →ₗ[R] A[X] :=
  LinearMap.toSpanSingleton A _ (aeval (Polynomial.X : A[X])).toLinearMap
