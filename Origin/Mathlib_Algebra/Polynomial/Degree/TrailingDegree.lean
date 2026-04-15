/-
Extracted from Algebra/Polynomial/Degree/TrailingDegree.lean
Genuine: 5 of 7 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Trailing degree of univariate polynomials

## Main definitions

* `trailingDegree p`: the multiplicity of `X` in the polynomial `p`
* `natTrailingDegree`: a variant of `trailingDegree` that takes values in the natural numbers
* `trailingCoeff`: the coefficient at index `natTrailingDegree p`

Converts most results about `degree`, `natDegree` and `leadingCoeff` to results about the bottom
end of a polynomial
-/

noncomputable section

open Function Polynomial Finsupp Finset

open scoped Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

def trailingDegree (p : R[X]) : ℕ∞ :=
  p.support.min

theorem trailingDegree_lt_wf : WellFounded fun p q : R[X] => trailingDegree p < trailingDegree q :=
  InvImage.wf trailingDegree wellFounded_lt

def natTrailingDegree (p : R[X]) : ℕ :=
  ENat.toNat (trailingDegree p)

def trailingCoeff (p : R[X]) : R :=
  coeff p (natTrailingDegree p)

def TrailingMonic (p : R[X]) :=
  trailingCoeff p = (1 : R)

-- INSTANCE (free from Core): TrailingMonic.decidable
