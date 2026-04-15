/-
Extracted from LinearAlgebra/Matrix/Trace.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Trace of a matrix

This file defines the trace of a matrix, the map sending a matrix to the sum of its diagonal
entries.

See also `LinearAlgebra.Trace` for the trace of an endomorphism.

## Tags

matrix, trace, diagonal

-/

open Matrix

namespace Matrix

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

section AddCommMonoid

variable [AddCommMonoid R]

def trace (A : Matrix n n R) : R :=
  ∑ i, diag A i
