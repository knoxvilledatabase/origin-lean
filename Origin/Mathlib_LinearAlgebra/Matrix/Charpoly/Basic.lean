/-
Extracted from LinearAlgebra/Matrix/Charpoly/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Characteristic polynomials and the Cayley-Hamilton theorem

We define characteristic polynomials of matrices and
prove the Cayley–Hamilton theorem over arbitrary commutative rings.

See the file `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean` for corollaries of this theorem.

## Main definitions

* `Matrix.charpoly` is the characteristic polynomial of a matrix.

## Implementation details

We follow a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/

noncomputable section

universe u v w

namespace Matrix

open Finset Matrix Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M
