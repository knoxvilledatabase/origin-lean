/-
Extracted from LinearAlgebra/SymplecticGroup.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Symplectic Group

This file defines the symplectic group and proves elementary properties.

## Main Definitions

* `Matrix.J`: the canonical `2n × 2n` skew-symmetric matrix
* `symplecticGroup`: the group of symplectic matrices

## TODO
* Every symplectic matrix has determinant 1.
* For `n = 1` the symplectic group coincides with the special linear group.
-/

open Matrix

variable {l R : Type*}

namespace Matrix

variable (l) [DecidableEq l] (R) [CommRing R]

section JMatrixLemmas

def J : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 0 (-1) 1 0
