/-
Extracted from LinearAlgebra/Matrix/Hermitian.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-! # Hermitian matrices

This file defines Hermitian matrices and some basic results about them.

See also `IsSelfAdjoint`, which generalizes this definition to other star rings.

## Main definition

* `Matrix.IsHermitian` : a matrix `A : Matrix n n α` is Hermitian if `Aᴴ = A`.

## Tags

self-adjoint matrix, hermitian matrix

-/

assert_not_exists NormedGroup

namespace Matrix

variable {α β m n : Type*} {A : Matrix n n α}

section Star

variable [Star α] [Star β]

def IsHermitian (A : Matrix n n α) : Prop := Aᴴ = A

-- INSTANCE (free from Core): (A

protected alias ⟨IsHermitian.isSelfAdjoint, _root_.IsSelfAdjoint.isHermitian⟩ :=

  isHermitian_iff_isSelfAdjoint

theorem IsHermitian.ext {A : Matrix n n α} : (∀ i j, star (A j i) = A i j) → A.IsHermitian := by
  intro h; ext i j; exact h i j

theorem IsHermitian.apply {A : Matrix n n α} (h : A.IsHermitian) (i j : n) : star (A j i) = A i j :=
  congr_fun (congr_fun h _) _

theorem IsHermitian.ext_iff {A : Matrix n n α} : A.IsHermitian ↔ ∀ i j, star (A j i) = A i j :=
  ⟨IsHermitian.apply, IsHermitian.ext⟩
