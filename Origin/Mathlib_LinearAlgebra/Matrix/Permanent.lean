/-
Extracted from LinearAlgebra/Matrix/Permanent.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Permanent of a matrix

This file defines the permanent of a matrix, `Matrix.permanent`, and some of its properties.

## Main definitions

* `Matrix.permanent`: the permanent of a square matrix, as a sum over permutations

-/

open Equiv Fintype Finset

namespace Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

def permanent (M : Matrix n n R) : R := ∑ σ : Perm n, ∏ i, M (σ i) i
