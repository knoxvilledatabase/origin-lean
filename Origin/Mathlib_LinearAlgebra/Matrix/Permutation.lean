/-
Extracted from LinearAlgebra/Matrix/Permutation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Permutation matrices

This file defines the matrix associated with a permutation

## Main definitions

- `Equiv.Perm.permMatrix`: the permutation matrix associated with an `Equiv.Perm`

## Main results

- `Matrix.det_permutation`: the determinant is the sign of the permutation
- `Matrix.trace_permutation`: the trace is the number of fixed points of the permutation

-/

open Equiv

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable (R) in

abbrev Equiv.Perm.permMatrix [Zero R] [One R] : Matrix n n R :=
  σ.toPEquiv.toMatrix

namespace Matrix
