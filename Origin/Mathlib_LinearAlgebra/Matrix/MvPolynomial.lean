/-
Extracted from LinearAlgebra/Matrix/MvPolynomial.lean
Genuine: 4 of 6 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrices of multivariate polynomials

In this file, we prove results about matrices over an mv_polynomial ring.
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

@[simp]
theorem mvPolynomialX_apply [CommSemiring R] (i j) :
    mvPolynomialX m n R i j = MvPolynomial.X (i, j) :=
  rfl

variable {m n R}

theorem mvPolynomialX_map_eval₂ [CommSemiring R] [CommSemiring S] (f : R →+* S) (A : Matrix m n S) :
    (mvPolynomialX m n R).map (MvPolynomial.eval₂ f fun p : m × n => A p.1 p.2) = A :=
  ext fun i j => MvPolynomial.eval₂_X _ (fun p : m × n => A p.1 p.2) (i, j)

theorem mvPolynomialX_mapMatrix_eval [Fintype m] [DecidableEq m] [CommSemiring R]
    (A : Matrix m m R) :
    (MvPolynomial.eval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A

variable (R)

theorem mvPolynomialX_mapMatrix_aeval [Fintype m] [DecidableEq m] [CommSemiring R] [CommSemiring S]
    [Algebra R S] (A : Matrix m m S) :
    (MvPolynomial.aeval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A

variable (m)

-- DISSOLVED: det_mvPolynomialX_ne_zero

end Matrix
