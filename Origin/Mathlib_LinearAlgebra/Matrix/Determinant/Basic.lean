/-
Extracted from LinearAlgebra/Matrix/Determinant/Basic.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Determinant of a matrix

This file defines the determinant of a matrix, `Matrix.det`, and its essential properties.

## Main definitions

- `Matrix.det`: the determinant of a square matrix, as a sum over permutations
- `Matrix.detRowAlternating`: the determinant, as an `AlternatingMap` in the rows of the matrix

## Main results

- `det_mul`: the determinant of `A * B` is the product of determinants
- `det_zero_of_row_eq`: the determinant is zero if there is a repeated row
- `det_block_diagonal`: the determinant of a block diagonal matrix is a product
  of the blocks' determinants

## Implementation notes

It is possible to configure `simp` to compute determinants. See the file
`MathlibTest/matrix.lean` for some examples.

-/

universe u v w z

open Equiv Equiv.Perm Finset Function

namespace Matrix

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

local notation "ε " σ:arg => ((sign σ : ℤ) : R)

def detRowAlternating : (n → R) [⋀^n]→ₗ[R] R :=
  MultilinearMap.alternatization ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj)

def det (M : Matrix n n R) : R :=
  detRowAlternating M

theorem det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i :=
  MultilinearMap.alternatization_apply _ M

theorem det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n, ε σ * ∏ i, M (σ i) i := by
  simp [det_apply, Units.smul_def]

theorem det_eq_detp_sub_detp (M : Matrix n n R) : M.det = M.detp 1 - M.detp (-1) := by
  rw [det_apply, ← Equiv.sum_comp (Equiv.inv (Perm n)), ← ofSign_disjUnion, sum_disjUnion]
  simp_rw [inv_apply, sign_inv, sub_eq_add_neg, detp, ← sum_neg_distrib]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ ↦ ?_) (sum_congr rfl fun σ hσ ↦ ?_) <;>
    rw [mem_ofSign.mp hσ, ← Equiv.prod_comp σ] <;> simp
