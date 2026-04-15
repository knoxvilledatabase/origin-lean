/-
Extracted from LinearAlgebra/Matrix/SpecialLinearGroup.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `SpecialLinearGroup n R`, consisting
of all square `R`-matrices with determinant `1` on the fintype `n` by `n`.  In addition, we define
the group structure on `SpecialLinearGroup n R` and the embedding into the general linear group
`GeneralLinearGroup R (n → R)`.

## Main definitions

* `Matrix.SpecialLinearGroup` is the type of matrices with determinant 1
* `Matrix.SpecialLinearGroup.group` gives the group structure (under multiplication)
* `Matrix.SpecialLinearGroup.toGL` is the embedding `SLₙ(R) → GLₙ(R)`

## Notation

For `m : ℕ`, we introduce the notation `SL(m,R)` for the special linear group on the fintype
`n = Fin m`, in the scope `MatrixGroups`.

## Implementation notes
The inverse operation in the `SpecialLinearGroup` is defined to be the adjugate
matrix, so that `SpecialLinearGroup n R` has a group structure for all `CommRing R`.

We define the elements of `SpecialLinearGroup` to be matrices, since we need to
compute their determinant. This is in contrast with `GeneralLinearGroup R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `Matrix.SpecialLinearGroup.hasCoeToFun` for convenience, but do not state any
lemmas about it, and use `Matrix.SpecialLinearGroup.coeFn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References

* https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/

namespace Matrix

universe u v

open LinearMap

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

def SpecialLinearGroup :=
  { A : Matrix n n R // A.det = 1 }

end
