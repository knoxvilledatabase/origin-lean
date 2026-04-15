/-
Extracted from RingTheory/MatrixAlgebra.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Algebra isomorphisms between tensor products and matrices

## Main definitions

* `matrixEquivTensor : Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
* `Matrix.kroneckerTMulAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃ₐ[S] Matrix (m × n) (m × n) (A ⊗[R] B)`,
  where the forward map is the (tensor-ified) Kronecker product.
-/

open TensorProduct Algebra.TensorProduct Matrix

variable {l m n p : Type*} {R S A B M N : Type*}

section Module

variable [CommSemiring R] [Semiring S] [Semiring A] [Semiring B] [AddCommMonoid M] [AddCommMonoid N]

variable [Algebra R S] [Algebra R A] [Algebra R B] [Module R M] [Module S M] [Module R N]

variable [IsScalarTower R S M]

variable [Fintype l] [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]

open Kronecker

variable (l m n p R S A M N)

attribute [local ext] ext_linearMap

def kroneckerTMulLinearEquiv :
    Matrix l m M ⊗[R] Matrix n p N ≃ₗ[S] Matrix (l × n) (m × p) (M ⊗[R] N) :=
  .ofLinear
    (AlgebraTensorModule.lift <| kroneckerTMulBilinear R S)
    (Matrix.liftLinear R fun ii jj =>
      AlgebraTensorModule.map (singleLinearMap S ii.1 jj.1) (singleLinearMap R ii.2 jj.2))
    (by
      ext : 4
      simp [single_kroneckerTMul_single])
    (by
      ext : 5
      simp [single_kroneckerTMul_single])
