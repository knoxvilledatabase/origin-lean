/-
Extracted from Algebra/Polynomial/Sequence.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Polynomial sequences

We define polynomial sequences – sequences of polynomials `a₀, a₁, ...` such that the polynomial
`aᵢ` has degree `i`.

## Main definitions

* `Polynomial.Sequence R`: the type of polynomial sequences with coefficients in `R`

## Main statements

* `Polynomial.Sequence.basis`: a sequence is a basis for `R[X]`

## TODO

Generalize linear independence to:
  * `IsCancelAdd` semirings
  * just require coefficients are regular
  * arbitrary sets of polynomials which are pairwise different degree.
-/

open Module Submodule

open scoped Function

variable (R : Type*)

namespace Polynomial

structure Sequence [Semiring R] where
  /-- The `i`-th element in the sequence. Use `S i` instead, defined via `CoeFun`. -/
  protected elems' : ℕ → R[X]
  /-- The `i`-th element in the sequence has degree `i`. Use `S.degree_eq` instead. -/
  protected degree_eq' (i : ℕ) : (elems' i).degree = i

attribute [coe] Sequence.elems'

namespace Sequence

variable {R}

-- INSTANCE (free from Core): coeFun

section Semiring

variable [Semiring R] (S : Sequence R)
