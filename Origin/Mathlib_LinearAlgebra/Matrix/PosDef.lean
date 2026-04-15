/-
Extracted from LinearAlgebra/Matrix/PosDef.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Positive Definite Matrices

This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms.
In `Mathlib/Analysis/Matrix/Order.lean`, positive semi-definiteness is used to define the partial
order on matrices on `ℝ` or `ℂ`.

## Main definitions

* `Matrix.PosSemidef` : a matrix `M : Matrix n n R` is positive semidefinite if it is Hermitian
  and `xᴴMx` is nonnegative for all `x`.
* `Matrix.PosDef` : a matrix `M : Matrix n n R` is positive definite if it is Hermitian and `xᴴMx`
  is greater than zero for all nonzero `x`.

## Main results

* `Matrix.PosSemidef.fromBlocks₁₁` and `Matrix.PosSemidef.fromBlocks₂₂`: If a matrix `A` is
  positive definite, then `[A B; Bᴴ D]` is positive semidefinite if and only if `D - Bᴴ A⁻¹ B` is
  positive semidefinite.
* `Matrix.PosDef.isUnit`: A positive definite matrix in a field is invertible.
-/

assert_not_exists NormedGroup

open Matrix

namespace Matrix

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

/-!
## Positive semidefinite matrices
-/

def PosSemidef (M : Matrix n n R) : Prop :=
  M.IsHermitian ∧ ∀ x : n →₀ R, 0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj

protected theorem PosSemidef.diagonal [StarOrderedRing R] [DecidableEq n] {d : n → R} (h : 0 ≤ d) :
    PosSemidef (diagonal d) where
  left := isHermitian_diagonal_of_self_adjoint _ <| funext fun i => IsSelfAdjoint.of_nonneg (h i)
  right x := by
    -- TODO: positivity
    refine Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ ?_
    simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _)]
