/-
Extracted from LinearAlgebra/Matrix/RowCol.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Row and column matrices

This file provides results about row and column matrices.

## Main definitions

* `Matrix.replicateRow ι r : Matrix ι n α`: the matrix where every row is the vector `r : n → α`
* `Matrix.replicateCol ι c : Matrix m ι α`: the matrix where every column is the vector `c : m → α`
* `Matrix.updateRow M i r`: update the `i`th row of `M` to `r`
* `Matrix.updateCol M j c`: update the `j`th column of `M` to `c`

-/

variable {l m n o : Type*}

universe u v w

variable {R : Type*} {α : Type v} {β : Type w}

namespace Matrix

def replicateCol (ι : Type*) (w : m → α) : Matrix m ι α :=
  of fun x _ => w x
