/-
Extracted from LinearAlgebra/Matrix/Block.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Block matrices and their determinant

This file defines a predicate `Matrix.BlockTriangular` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

* `Matrix.BlockTriangular` expresses that an `o` by `o` matrix is block triangular,
  if the rows and columns are ordered according to some order `b : o → α`

## Main results

* `Matrix.det_of_blockTriangular`: the determinant of a block triangular matrix
  is equal to the product of the determinants of all the blocks
* `Matrix.det_of_upperTriangular` and `Matrix.det_of_lowerTriangular`: the determinant of
  a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/

open Finset Function OrderDual

open Matrix

universe v

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

namespace Matrix

section LT

variable [LT α]

section Zero

variable [Zero R]

def BlockTriangular (M : Matrix m m R) (b : m → α) : Prop :=
  ∀ ⦃i j⦄, b j < b i → M i j = 0
