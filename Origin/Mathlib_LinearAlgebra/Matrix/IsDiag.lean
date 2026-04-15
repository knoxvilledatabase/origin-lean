/-
Extracted from LinearAlgebra/Matrix/IsDiag.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Diagonal matrices

This file contains the definition and basic results about diagonal matrices.

## Main results

- `Matrix.IsDiag`: a proposition that states a given square matrix `A` is diagonal.

## Tags

diag, diagonal, matrix
-/

namespace Matrix

variable {α β R n m : Type*}

open Function

open Matrix Kronecker

def IsDiag [Zero α] (A : Matrix n n α) : Prop :=
  Pairwise fun i j => A i j = 0
