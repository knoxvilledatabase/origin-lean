/-
Extracted from Data/Matrix/Mul.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matrix multiplication

This file defines vector and matrix multiplication

## Main definitions
* `dotProduct`: the dot product between two vectors
* `Matrix.mul`: multiplication of two matrices
* `Matrix.mulVec`: multiplication of a matrix with a vector
* `Matrix.vecMul`: multiplication of a vector with a matrix
* `Matrix.vecMulVec`: multiplication of a vector with a vector to get a matrix
* `Matrix.instRing`: square matrices form a ring

## Notation

The scope `Matrix` gives the following notation:

* `⬝ᵥ` for `dotProduct`
* `*ᵥ` for `Matrix.mulVec`
* `ᵥ*` for `Matrix.vecMul`

See `Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean` for

* `ᴴ` for `Matrix.conjTranspose`

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/

assert_not_exists Algebra Field TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

open Matrix

section DotProduct

variable [Fintype m] [Fintype n]

def dotProduct [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
  ∑ i, v i * w i
