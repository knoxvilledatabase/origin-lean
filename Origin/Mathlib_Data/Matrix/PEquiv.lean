/-
Extracted from Data/Matrix/PEquiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# partial equivalences for matrices

Using partial equivalences to represent matrices.
This file introduces the function `PEquiv.toMatrix`, which returns a matrix containing ones and
zeros. For any partial equivalence `f`, `f.toMatrix i j = 1 ↔ f i = some j`.

The following important properties of this function are proved
`toMatrix_trans : (f.trans g).toMatrix = f.toMatrix * g.toMatrix`
`toMatrix_symm  : f.symm.toMatrix = f.toMatrixᵀ`
`toMatrix_refl : (PEquiv.refl n).toMatrix = 1`
`toMatrix_bot : ⊥.toMatrix = 0`

This theory gives the matrix representation of projection linear maps, and their right inverses.
For example, the matrix `(single (0 : Fin 1) (i : Fin n)).toMatrix` corresponds to the ith
projection map from R^n to R.

Any injective function `Fin m → Fin n` gives rise to a `PEquiv`, whose matrix is the projection
map from R^m → R^n represented by the same function. The transpose of this matrix is the right
inverse of this map, sending anything not in the image to zero.

## Notation

This file uses `ᵀ` for `Matrix.transpose`.
-/

assert_not_exists Field

namespace PEquiv

open Matrix

universe u v

variable {k l m n : Type*}

variable {α β : Type*}

open Matrix

def toMatrix [DecidableEq n] [Zero α] [One α] (f : m ≃. n) : Matrix m n α :=
  of fun i j => if j ∈ f i then (1 : α) else 0
