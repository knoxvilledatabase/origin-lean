/-
Extracted from Data/Matrix/Invertible.lean
Genuine: 15 of 17 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Tactic.Abel

/-! # Extra lemmas about invertible matrices

A few of the `Invertible` lemmas generalize to multiplication of rectangular matrices.

For lemmas about the matrix inverse in terms of the determinant and adjugate, see `Matrix.inv`
in `LinearAlgebra/Matrix/NonsingularInverse.lean`.

## Main results

* `Matrix.invertibleConjTranspose`
* `Matrix.invertibleTranspose`
* `Matrix.isUnit_conjTranpose`
* `Matrix.isUnit_tranpose`
-/

open scoped Matrix

variable {m n : Type*} {α : Type*}

variable [Fintype n] [DecidableEq n]

namespace Matrix

section Semiring

variable [Semiring α]

protected theorem invOf_mul_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    ⅟ A * (A * B) = B := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

protected theorem mul_invOf_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    A * (⅟ A * B) = B := by rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]

protected theorem invOf_mul_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * ⅟ B * B = A := by rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]

protected theorem mul_invOf_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * B * ⅟ B = A := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]

protected alias invOf_mul_self_assoc := Matrix.invOf_mul_cancel_left

protected alias mul_invOf_self_assoc := Matrix.mul_invOf_cancel_left

protected alias mul_invOf_mul_self_cancel := Matrix.invOf_mul_cancel_right

protected alias mul_mul_invOf_self_cancel := Matrix.mul_invOf_cancel_right

section ConjTranspose

variable [StarRing α] (A : Matrix n n α)

instance invertibleConjTranspose [Invertible A] : Invertible Aᴴ := Invertible.star _

lemma conjTranspose_invOf [Invertible A] [Invertible Aᴴ] : (⅟A)ᴴ = ⅟(Aᴴ) := star_invOf _

def invertibleOfInvertibleConjTranspose [Invertible Aᴴ] : Invertible A := by
  rw [← conjTranspose_conjTranspose A, ← star_eq_conjTranspose]
  infer_instance

@[simp] lemma isUnit_conjTranspose : IsUnit Aᴴ ↔ IsUnit A := isUnit_star

end ConjTranspose

end Semiring

section CommSemiring

variable [CommSemiring α] (A : Matrix n n α)

instance invertibleTranspose [Invertible A] : Invertible Aᵀ where
  invOf := (⅟A)ᵀ
  invOf_mul_self := by rw [← transpose_mul, mul_invOf_self, transpose_one]
  mul_invOf_self := by rw [← transpose_mul, invOf_mul_self, transpose_one]

lemma transpose_invOf [Invertible A] [Invertible Aᵀ] : (⅟A)ᵀ = ⅟(Aᵀ) := by
  letI := invertibleTranspose A
  convert (rfl : _ = ⅟(Aᵀ))

def invertibleOfInvertibleTranspose [Invertible Aᵀ] : Invertible A where
  invOf := (⅟(Aᵀ))ᵀ
  invOf_mul_self := by rw [← transpose_one, ← mul_invOf_self Aᵀ, transpose_mul, transpose_transpose]
  mul_invOf_self := by rw [← transpose_one, ← invOf_mul_self Aᵀ, transpose_mul, transpose_transpose]

@[simps]
def transposeInvertibleEquivInvertible : Invertible Aᵀ ≃ Invertible A where
  toFun := @invertibleOfInvertibleTranspose _ _ _ _ _ _
  invFun := @invertibleTranspose _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

@[simp] lemma isUnit_transpose : IsUnit Aᵀ ↔ IsUnit A := by
  simp only [← nonempty_invertible_iff_isUnit,
    (transposeInvertibleEquivInvertible A).nonempty_congr]

end CommSemiring

section Ring

section Woodbury

variable [Fintype m] [DecidableEq m] [Ring α]
    (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)
    [Invertible A] [Invertible C] [Invertible (⅟C + V * ⅟A * U)]

lemma add_mul_mul_invOf_mul_eq_one :
    (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) = 1 := by
  calc
    (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)
    _ = A*⅟A - A*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A - U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      simp_rw [add_sub_assoc, add_mul, mul_sub, Matrix.mul_assoc]
    _ = (1 + U*C*V*⅟A) - (U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) := by
      rw [mul_invOf_self, Matrix.one_mul]
      abel
    _ = 1 + U*C*V*⅟A - (U + U*C*V*⅟A*U)*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      rw [sub_right_inj, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul]
    _ = 1 + U*C*V*⅟A - U*C*(⅟C + V*⅟A*U)*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      congr
      simp only [Matrix.mul_add, Matrix.mul_invOf_cancel_right, ← Matrix.mul_assoc]
    _ = 1 := by
      rw [Matrix.mul_invOf_cancel_right]
      abel

lemma add_mul_mul_invOf_mul_eq_one' :
    (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V) = 1 := by
  calc
    (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V)
    _ = ⅟A*A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*A + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*U*C*V := by
      simp_rw [add_sub_assoc, _root_.mul_add, _root_.sub_mul, Matrix.mul_assoc]
    _ = (1 + ⅟A*U*C*V) - (⅟A*U*⅟(⅟C + V*⅟A*U)*V + ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*U*C*V) := by
      rw [invOf_mul_self, Matrix.invOf_mul_cancel_right]
      abel
    _ = 1 + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*(V + V*⅟A*U*C*V) := by
      rw [sub_right_inj, Matrix.mul_add]
      simp_rw [Matrix.mul_assoc]
    _ = 1 + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*(⅟C + V*⅟A*U)*C*V := by
      congr 1
      simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc,
        Matrix.invOf_mul_cancel_right]
    _ = 1 := by
      rw [Matrix.invOf_mul_cancel_right]
      abel

def invertibleAddMulMul : Invertible (A + U*C*V) where
  invOf := ⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A
  invOf_mul_self := add_mul_mul_invOf_mul_eq_one' _ _ _ _
  mul_invOf_self := add_mul_mul_invOf_mul_eq_one _ _ _ _

theorem invOf_add_mul_mul [Invertible (A + U*C*V)] :
    ⅟(A + U*C*V) = ⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A := by
  letI := invertibleAddMulMul A U C V
  convert (rfl : ⅟(A + U*C*V) = _)

end Woodbury

end Ring

end Matrix
