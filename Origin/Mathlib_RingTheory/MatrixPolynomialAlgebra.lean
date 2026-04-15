/-
Extracted from RingTheory/MatrixPolynomialAlgebra.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Algebra isomorphism between matrices of polynomials and polynomials of matrices

We obtain the algebra isomorphism
```
def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X]
```
which is characterized by
```
coeff (matPolyEquiv m) k i j = coeff (m i j) k
```

We will use this algebra isomorphism to prove the Cayley-Hamilton theorem.
-/

universe u v w

open Polynomial TensorProduct

open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R A : Type*)

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

open Matrix

variable {R}

variable {n : Type w} [DecidableEq n] [Fintype n]

noncomputable def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X] :=
  ((matrixEquivTensor n R R[X]).trans (Algebra.TensorProduct.comm R _ _)).trans
    (polyEquivTensor R (Matrix n n R)).symm
