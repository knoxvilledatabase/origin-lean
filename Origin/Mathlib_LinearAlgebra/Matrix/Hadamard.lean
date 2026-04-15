/-
Extracted from LinearAlgebra/Matrix/Hadamard.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Hadamard product of matrices

This file defines the Hadamard product `Matrix.hadamard`
and contains basic properties about them.

## Main definition

- `Matrix.hadamard`: defines the Hadamard product,
  which is the pointwise product of two matrices of the same size.

## Notation

* `⊙`: the Hadamard product `Matrix.hadamard`;

## References

* <https://en.wikipedia.org/wiki/hadamard_product_(matrices)>

## Tags

hadamard product, hadamard
-/

variable {α m n R : Type*}

namespace Matrix

def hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α :=
  of fun i j => A i j * B i j
