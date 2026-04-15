/-
Extracted from Algebra/Polynomial/Inductions.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Induction on polynomials

This file contains lemmas dealing with different flavours of induction on polynomials.
-/

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

def divX (p : R[X]) : R[X] :=
  ⟨AddMonoidAlgebra.divOf p.toFinsupp 1⟩
