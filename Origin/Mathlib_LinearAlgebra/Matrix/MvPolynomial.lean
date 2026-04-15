/-
Extracted from LinearAlgebra/Matrix/MvPolynomial.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matrices of multivariate polynomials

In this file, we prove results about matrices over an `MvPolynomial` ring.
In particular, we provide `Matrix.mvPolynomialX` which associates every entry of a matrix with a
unique variable.

## Tags

matrix determinant, multivariate polynomial
-/

variable {m n R S : Type*}

namespace Matrix

variable (m n R)

noncomputable def mvPolynomialX [CommSemiring R] : Matrix m n (MvPolynomial (m × n) R) :=
  of fun i j => MvPolynomial.X (i, j)
