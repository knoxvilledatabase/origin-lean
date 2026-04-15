/-
Extracted from Data/Matrix/Basis.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matrices with a single non-zero element.

This file provides `Matrix.single`. The matrix `Matrix.single i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
-/

assert_not_exists Matrix.trace

variable {l m n o : Type*}

variable {R S α β γ : Type*}

namespace Matrix

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq o]

section Zero

variable [Zero α]

def single (i : m) (j : n) (a : α) : Matrix m n α :=
  of <| fun i' j' => if i = i' ∧ j = j' then a else 0

variable (i : m) (j : n) (c : α) (i' : m) (j' : n)
