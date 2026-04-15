/-
Extracted from LinearAlgebra/Matrix/Orthogonal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Orthogonal

This file contains definitions and properties concerning orthogonality of rows and columns.

## Main results

- `matrix.HasOrthogonalRows`:
  `A.HasOrthogonalRows` means `A` has orthogonal (with respect to `dotProduct`) rows.
- `matrix.HasOrthogonalCols`:
  `A.HasOrthogonalCols` means `A` has orthogonal (with respect to `dotProduct`) columns.

## Tags

orthogonal
-/

assert_not_exists Field

namespace Matrix

variable {α n m : Type*}

variable [Mul α] [AddCommMonoid α]

variable (A : Matrix m n α)

open Matrix

def HasOrthogonalRows [Fintype n] : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → A i₁ ⬝ᵥ A i₂ = 0

def HasOrthogonalCols [Fintype m] : Prop :=
  HasOrthogonalRows Aᵀ
