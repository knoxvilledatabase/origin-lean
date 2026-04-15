/-
Extracted from LinearAlgebra/Matrix/Swap.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Swap matrices

A swap matrix indexed by `i` and `j` is the matrix that, when multiplying another matrix
on the left (resp. on the right), swaps the `i`-th row with the `j`-th row
(resp. the `i`-th column with the `j`-th column).

Swap matrices are a special case of *elementary matrices*. For transvections see
`Mathlib/LinearAlgebra/Matrix/Transvection.lean`.

## Implementation detail

This is a thin wrapper around `(Equiv.swap i j).permMatrix`.
-/

namespace Matrix

section Def

variable {R n : Type*} [Zero R] [One R] [DecidableEq n]

variable (R) in

def swap (i j : n) : Matrix n n R :=
  (Equiv.swap i j).permMatrix R

lemma swap_comm (i j : n) :
    swap R i j = swap R j i := by
  simp only [swap, Equiv.swap_comm]
