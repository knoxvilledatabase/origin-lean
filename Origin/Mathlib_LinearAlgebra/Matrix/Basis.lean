/-
Extracted from LinearAlgebra/Matrix/Basis.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Bases and matrices

This file defines the map `Basis.toMatrix` that sends a family of vectors to
the matrix of their coordinates with respect to some basis.

## Main definitions

* `Basis.toMatrix e v` is the matrix whose `i, j`th entry is `e.repr (v j) i`
* `basis.toMatrixEquiv` is `Basis.toMatrix` bundled as a linear equiv

## Main results

* `LinearMap.toMatrix_id_eq_basis_toMatrix`: `LinearMap.toMatrix b c id`
  is equal to `Basis.toMatrix b c`
* `Basis.toMatrix_mul_toMatrix`: multiplying `Basis.toMatrix` with another
  `Basis.toMatrix` gives a `Basis.toMatrix`

## Tags

matrix, basis
-/

noncomputable section

open Function LinearMap Matrix Module Set Submodule

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

namespace Module.Basis

def toMatrix (e : Basis ι R M) (v : ι' → M) : Matrix ι ι' R := fun i j ↦ e.repr (v j) i

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

theorem toMatrix_transpose_apply : (e.toMatrix v)ᵀ j = e.repr (v j) :=
  funext fun _ => rfl

theorem toMatrix_eq_toMatrix_constr [Fintype ι] [DecidableEq ι] (v : ι → M) :
    e.toMatrix v = LinearMap.toMatrix e e (e.constr ℕ v) := by
  ext
  rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply, Basis.constr_basis]

theorem coePiBasisFun.toMatrix_eq_transpose [Finite ι] :
    ((Pi.basisFun R ι).toMatrix : Matrix ι ι R → Matrix ι ι R) = Matrix.transpose := by
  ext M i j
  rfl
