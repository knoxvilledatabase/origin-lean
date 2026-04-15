/-
Extracted from LinearAlgebra/Matrix/SemiringInverse.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Nonsingular inverses over semirings

This file proves `A * B = 1 ↔ B * A = 1` for square matrices over a commutative semiring.

-/

open Equiv Equiv.Perm Finset

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

namespace Matrix

def detp : R := ∑ σ ∈ ofSign s, ∏ k, A k (σ k)
