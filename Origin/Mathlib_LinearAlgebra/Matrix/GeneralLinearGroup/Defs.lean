/-
Extracted from LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The General Linear group $GL(n, R)$

This file defines the elements of the General Linear group `Matrix.GeneralLinearGroup n R`,
consisting of all invertible `n` by `n` `R`-matrices.

## Main definitions

* `Matrix.GeneralLinearGroup` is the type of matrices over R which are units in the matrix ring.
* `Matrix.GLPos` gives the subgroup of matrices with
  positive determinant (over a linear ordered ring).

## Tags

matrix group, group, matrix inverse
-/

namespace Matrix

universe u v

open Matrix

open LinearMap

abbrev GeneralLinearGroup (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [Semiring R] :
    Type _ :=
  (Matrix n n R)ˣ
