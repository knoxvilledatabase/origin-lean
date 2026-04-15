/-
Extracted from Data/Matrix/Invertible.lean
Genuine: 9 of 10 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Extra lemmas about invertible matrices

A few of the `Invertible` lemmas generalize to multiplication of rectangular matrices.

For lemmas about the matrix inverse in terms of the determinant and adjugate, see `Matrix.inv`
in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`.

## Main results

* `Matrix.invertibleConjTranspose`
* `Matrix.invertibleTranspose`
* `Matrix.isUnit_conjTranspose`
* `Matrix.isUnit_transpose`
-/

open scoped Matrix

variable {m n : Type*} {α : Type*}

variable [Fintype n] [DecidableEq n]

namespace Matrix

section Semiring

variable [Semiring α]

protected theorem invOf_mul_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    ⅟A * (A * B) = B := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

protected theorem mul_invOf_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    A * (⅟A * B) = B := by rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]

protected theorem invOf_mul_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * ⅟B * B = A := by rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]

protected theorem mul_invOf_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * B * ⅟B = A := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]

protected theorem invOf_mul_eq_iff_eq_mul_left
    {A B : Matrix n m α} {C : Matrix n n α} [Invertible C] :
    ⅟C * A = B ↔ A = C * B := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, Matrix.mul_invOf_cancel_left]
  · rw [h, Matrix.invOf_mul_cancel_left]

protected theorem mul_left_eq_iff_eq_invOf_mul
    {A B : Matrix n m α} {C : Matrix n n α} [Invertible C] :
    C * A = B ↔ A = ⅟C * B := by
  rw [eq_comm, ← Matrix.invOf_mul_eq_iff_eq_mul_left, eq_comm]

protected theorem mul_invOf_eq_iff_eq_mul_right
    {A B : Matrix m n α} {C : Matrix n n α} [Invertible C] :
    A * ⅟C = B ↔ A = B * C := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, Matrix.invOf_mul_cancel_right]
  · rw [h, Matrix.mul_invOf_cancel_right]

protected theorem mul_right_eq_iff_eq_mul_invOf
    {A B : Matrix m n α} {C : Matrix n n α} [Invertible C] :
    A * C = B ↔ A = B * ⅟C := by
  rw [eq_comm, ← Matrix.mul_invOf_eq_iff_eq_mul_right, eq_comm]

section ConjTranspose

variable [StarRing α] (A : Matrix n n α)

-- INSTANCE (free from Core): invertibleConjTranspose

lemma conjTranspose_invOf [Invertible A] [Invertible Aᴴ] : (⅟A)ᴴ = ⅟(Aᴴ) := star_invOf _
