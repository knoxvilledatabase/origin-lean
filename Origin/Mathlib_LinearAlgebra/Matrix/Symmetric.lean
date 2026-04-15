/-
Extracted from LinearAlgebra/Matrix/Symmetric.lean
Genuine: 8 of 10 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Symmetric matrices

This file contains the definition and basic results about symmetric matrices.

## Main definition

* `Matrix.isSymm`: a matrix `A : Matrix n n α` is "symmetric" if `Aᵀ = A`.

## Tags

symm, symmetric, matrix
-/

variable {α β n m R : Type*}

namespace Matrix

def IsSymm (A : Matrix n n α) : Prop :=
  Aᵀ = A

-- INSTANCE (free from Core): (A

theorem IsSymm.ext_iff {A : Matrix n n α} : A.IsSymm ↔ ∀ i j, A j i = A i j :=
  Matrix.ext_iff.symm

theorem IsSymm.ext {A : Matrix n n α} : (∀ i j, A j i = A i j) → A.IsSymm :=
  Matrix.ext

theorem IsSymm.apply {A : Matrix n n α} (h : A.IsSymm) (i j : n) : A j i = A i j :=
  IsSymm.ext_iff.1 h i j

theorem isSymm_mul_transpose_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
    (A * Aᵀ).IsSymm :=
  transpose_mul _ _

theorem isSymm_transpose_mul_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
    (Aᵀ * A).IsSymm :=
  transpose_mul _ _

theorem isSymm_add_transpose_self [AddCommSemigroup α] (A : Matrix n n α) : (A + Aᵀ).IsSymm :=
  add_comm _ _

theorem isSymm_transpose_add_self [AddCommSemigroup α] (A : Matrix n n α) : (Aᵀ + A).IsSymm :=
  add_comm _ _
