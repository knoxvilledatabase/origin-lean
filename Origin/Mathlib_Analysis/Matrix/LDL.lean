/-
Extracted from Analysis/Matrix/LDL.lean
Genuine: 9 of 10 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # LDL decomposition

This file proves the LDL-decomposition of matrices: Any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.

## Main definitions

* `LDL.lower` is the lower triangular matrix `L`.
* `LDL.lowerInv` is the inverse of the lower triangular matrix `L`.
* `LDL.diag` is the diagonal matrix `D`.

## Main result

* `LDL.lower_conj_diag` states that any positive definite matrix can be decomposed as `LDLᴴ`.

## TODO

* Prove that `LDL.lower` is lower triangular from `LDL.lowerInv_triangular`.

-/

open Module

variable {𝕜 : Type*} [RCLike 𝕜]

variable {n : Type*} [LinearOrder n] [WellFoundedLT n] [LocallyFiniteOrderBot n]

section set_options

set_option quotPrecheck false

local notation "⟪" x ", " y "⟫ₑ" => inner 𝕜 (WithLp.toLp 2 x) (WithLp.toLp 2 y)

open Matrix InnerProductSpace

open scoped ComplexOrder

variable {S : Matrix n n 𝕜} [Fintype n] (hS : S.PosDef)

noncomputable def LDL.lowerInv : Matrix n n 𝕜 :=
  @gramSchmidt 𝕜 (n → 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n)

theorem LDL.lowerInv_eq_gramSchmidtBasis :
    LDL.lowerInv hS =
      ((Pi.basisFun 𝕜 n).toMatrix
          (@gramSchmidtBasis 𝕜 (n → 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
            (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n)))ᵀ := by
  letI := (Sᵀ.toNormedAddCommGroup hS.transpose)
  letI := (Sᵀ.toInnerProductSpace hS.transpose.posSemidef)
  ext i j
  rw [LDL.lowerInv, Basis.coePiBasisFun.toMatrix_eq_transpose, coe_gramSchmidtBasis]
  rfl

-- INSTANCE (free from Core): LDL.invertibleLowerInv

theorem LDL.lowerInv_orthogonal {i j : n} (h₀ : i ≠ j) :
    ⟪LDL.lowerInv hS i, Sᵀ *ᵥ LDL.lowerInv hS j⟫ₑ = 0 :=
  @gramSchmidt_orthogonal 𝕜 _ _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) _ _ _ _ _ _ _ h₀

noncomputable def LDL.diagEntries : n → 𝕜 := fun i =>
  ⟪star (LDL.lowerInv hS i), S *ᵥ star (LDL.lowerInv hS i)⟫ₑ

noncomputable def LDL.diag : Matrix n n 𝕜 :=
  Matrix.diagonal (LDL.diagEntries hS)

theorem LDL.lowerInv_triangular {i j : n} (hij : i < j) : LDL.lowerInv hS i j = 0 := by
  rw [← @gramSchmidt_triangular 𝕜 (n → 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
      (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ i j hij (Pi.basisFun 𝕜 n),
    Pi.basisFun_repr, LDL.lowerInv]

theorem LDL.diag_eq_lowerInv_conj : LDL.diag hS = LDL.lowerInv hS * S * (LDL.lowerInv hS)ᴴ := by
  ext i j
  by_cases hij : i = j
  · simp only [diag, diagEntries, EuclideanSpace.inner_toLp_toLp, star_star, hij,
      diagonal_apply_eq, Matrix.mul_assoc, dotProduct_comm]
    rfl
  · simp only [LDL.diag, hij, diagonal_apply_ne, Ne, not_false_iff, mul_mul_apply]
    rw [conjTranspose, transpose_map, transpose_transpose, dotProduct_mulVec,
      (LDL.lowerInv_orthogonal hS fun h : j = i => hij h.symm).symm, ← inner_conj_symm,
      mulVec_transpose, EuclideanSpace.inner_toLp_toLp, ← RCLike.star_def, ←
      star_dotProduct_star, star_star]
    rfl

noncomputable def LDL.lower :=
  (LDL.lowerInv hS)⁻¹

theorem LDL.lower_conj_diag : LDL.lower hS * LDL.diag hS * (LDL.lower hS)ᴴ = S := by
  rw [LDL.lower, conjTranspose_nonsing_inv, Matrix.mul_assoc,
    Matrix.inv_mul_eq_iff_eq_mul_of_invertible (LDL.lowerInv hS),
    Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  exact LDL.diag_eq_lowerInv_conj hS

end set_options
