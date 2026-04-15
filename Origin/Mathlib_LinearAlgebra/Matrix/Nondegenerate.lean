/-
Extracted from LinearAlgebra/Matrix/Nondegenerate.lean
Genuine: 2 of 6 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Matrices associated with non-degenerate bilinear forms

## Main definitions

* `Matrix.Nondegenerate A`: the proposition that when interpreted as a bilinear form, the matrix `A`
  is nondegenerate.

-/

namespace Matrix

variable {m R A : Type*} [Fintype m] [CommRing R]

def Nondegenerate (M : Matrix m m R) :=
  ∀ v, (∀ w, Matrix.dotProduct v (M *ᵥ w) = 0) → v = 0

theorem Nondegenerate.eq_zero_of_ortho {M : Matrix m m R} (hM : Nondegenerate M) {v : m → R}
    (hv : ∀ w, Matrix.dotProduct v (M *ᵥ w) = 0) : v = 0 :=
  hM v hv

-- DISSOLVED: Nondegenerate.exists_not_ortho_of_ne_zero

variable [CommRing A] [IsDomain A]

-- DISSOLVED: nondegenerate_of_det_ne_zero

-- DISSOLVED: eq_zero_of_vecMul_eq_zero

-- DISSOLVED: eq_zero_of_mulVec_eq_zero

end Matrix
