/-
Extracted from LinearAlgebra/Determinant.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Determinant of families of vectors

This file defines the determinant of an endomorphism, and of a family of vectors
with respect to some basis. For the determinant of a matrix, see the file
`LinearAlgebra.Matrix.Determinant`.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

* `Basis.det`: the determinant of a family of vectors with respect to a basis,
  as a multilinear map
* `LinearMap.det`: the determinant of an endomorphism `f : End R M` as a
  multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
  result is `1` instead)
* `LinearEquiv.det`: the determinant of an isomorphism `f : M ≃ₗ[R] M` as a
  multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
  result is `1` instead)

## Tags

basis, det, determinant
-/

noncomputable section

open Matrix Module LinearMap Submodule Set Function

universe u v w

variable {R : Type*} [CommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {M' : Type*} [AddCommGroup M'] [Module R M']

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable (e : Basis ι R M)

section Conjugate

variable {A : Type*} [CommRing A]

variable {m n : Type*}

def equivOfPiLEquivPi {R : Type*} [Finite m] [Finite n] [CommRing R] [Nontrivial R]
    (e : (m → R) ≃ₗ[R] n → R) : m ≃ n :=
  Basis.indexEquiv (Basis.ofEquivFun e.symm) (Pi.basisFun _ _)

namespace Matrix

variable [Fintype m] [Fintype n]

def indexEquivOfInv [Nontrivial A] [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
    {M' : Matrix n m A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : m ≃ n :=
  equivOfPiLEquivPi (toLin'OfInv hMM' hM'M)

theorem det_comm [DecidableEq n] (M N : Matrix n n A) : det (M * N) = det (N * M) := by
  rw [det_mul, det_mul, mul_comm]

theorem det_comm' [DecidableEq m] [DecidableEq n] {M : Matrix n m A} {N : Matrix m n A}
    {M' : Matrix m n A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : det (M * N) = det (N * M) := by
  nontriviality A
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e := indexEquivOfInv hMM' hM'M
  rw [← det_submatrix_equiv_self e, ← submatrix_mul_equiv _ _ _ (Equiv.refl n) _, det_comm,
    submatrix_mul_equiv, Equiv.coe_refl, submatrix_id_id]

theorem det_conj_of_mul_eq_one [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
    {M' : Matrix n m A} {N : Matrix n n A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) :
    det (M * N * M') = det N := by
  rw [← det_comm' hM'M hMM', ← Matrix.mul_assoc, hM'M, Matrix.one_mul]

end Matrix

end Conjugate

namespace LinearMap

/-! ### Determinant of a linear map -/

variable {A : Type*} [CommRing A] [Module A M]

variable {κ : Type*} [Fintype κ]

theorem det_toMatrix_eq_det_toMatrix [DecidableEq κ] (b : Basis ι A M) (c : Basis κ A M)
    (f : M →ₗ[A] M) : det (LinearMap.toMatrix b b f) = det (LinearMap.toMatrix c c f) := by
  rw [← linearMap_toMatrix_mul_basis_toMatrix c b c, ← basis_toMatrix_mul_linearMap_toMatrix b c b,
      Matrix.det_conj_of_mul_eq_one] <;>
    rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]

irreducible_def detAux : Trunc (Basis ι A M) → (M →ₗ[A] M) →* A :=
  Trunc.lift
    (fun b : Basis ι A M => detMonoidHom.comp (toMatrixAlgEquiv b : (M →ₗ[A] M) →* Matrix ι ι A))
    fun b c => MonoidHom.ext <| det_toMatrix_eq_det_toMatrix b c

theorem detAux_def' (b : Basis ι A M) (f : M →ₗ[A] M) :
    LinearMap.detAux (Trunc.mk b) f = Matrix.det (LinearMap.toMatrix b b f) := by
  rw [detAux]
  rfl

theorem detAux_def'' {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (tb : Trunc <| Basis ι A M)
    (b' : Basis ι' A M) (f : M →ₗ[A] M) :
    LinearMap.detAux tb f = Matrix.det (LinearMap.toMatrix b' b' f) := by
  induction tb using Trunc.induction_on with
  | h b => rw [detAux_def', det_toMatrix_eq_det_toMatrix b b']
