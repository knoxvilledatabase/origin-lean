/-
Extracted from LinearAlgebra/Matrix/SchurComplement.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # 2×2 block matrices and the Schur complement

This file proves properties of 2×2 block matrices `[A B; C D]` that relate to the Schur complement
`D - C*A⁻¹*B`.

Some of the results here generalize to 2×2 matrices in a category, rather than just a ring. A few
results in this direction can be found in `Mathlib/CategoryTheory/Preadditive/Biproducts.lean`,
especially the declarations `CategoryTheory.Biprod.gaussian` and `CategoryTheory.Biprod.isoElim`.
Compare with `Matrix.invertibleOfFromBlocks₁₁Invertible`.

## Main results

* `Matrix.det_fromBlocks₁₁`, `Matrix.det_fromBlocks₂₂`: determinant of a block matrix in terms of
  the Schur complement.
* `Matrix.invOf_fromBlocks_zero₂₁_eq`, `Matrix.invOf_fromBlocks_zero₁₂_eq`: the inverse of a
  block triangular matrix.
* `Matrix.isUnit_fromBlocks_zero₂₁`, `Matrix.isUnit_fromBlocks_zero₁₂`: invertibility of a
  block triangular matrix.
* `Matrix.det_one_add_mul_comm`: the **Weinstein–Aronszajn identity**.

-/

variable {l m n α : Type*}

namespace Matrix

open scoped Matrix

section CommRing

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

theorem fromBlocks_eq_of_invertible₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix l m α)
    (D : Matrix l n α) [Invertible A] :
    fromBlocks A B C D =
      fromBlocks 1 0 (C * ⅟A) 1 * fromBlocks A 0 0 (D - C * ⅟A * B) *
        fromBlocks 1 (⅟A * B) 0 1 := by
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one, invOf_mul_self, Matrix.mul_invOf_cancel_left,
    Matrix.mul_assoc, add_sub_cancel]

theorem fromBlocks_eq_of_invertible₂₂ (A : Matrix l m α) (B : Matrix l n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] :
    fromBlocks A B C D =
      fromBlocks 1 (B * ⅟D) 0 1 * fromBlocks (A - B * ⅟D * C) 0 0 D *
        fromBlocks 1 0 (⅟D * C) 1 :=
  (Matrix.reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _)).injective <| by
    simpa [reindex_apply, Equiv.sumComm_symm, ← submatrix_mul_equiv _ _ _ (Equiv.sumComm n m), ←
      submatrix_mul_equiv _ _ _ (Equiv.sumComm n l), Equiv.sumComm_apply,
      fromBlocks_submatrix_sum_swap_sum_swap] using fromBlocks_eq_of_invertible₁₁ D C B A

section Triangular

/-! #### Block triangular matrices -/
