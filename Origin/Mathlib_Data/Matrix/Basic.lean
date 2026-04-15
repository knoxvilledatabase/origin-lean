/-
Extracted from Data/Matrix/Basic.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Matrices

This file contains basic results on matrices including bundled versions of matrix operators.

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/

assert_not_exists TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R S T A α β γ : Type*}

namespace Matrix

-- INSTANCE (free from Core): decidableEq

-- INSTANCE (free from Core): {n

-- INSTANCE (free from Core): {n

-- INSTANCE (free from Core): (priority

variable (R)

def ofLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] : (m → n → α) ≃ₗ[R] Matrix m n α where
  __ := ofAddEquiv
  map_smul' _ _ := rfl
