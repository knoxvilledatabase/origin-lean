/-
Extracted from Algebra/MvPolynomial/PDeriv.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `MvPolynomial.pderiv i p` : the partial derivative of `p` with respect to `i`, as a bundled
  derivation of `MvPolynomial σ R`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommRing R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/

noncomputable section

universe u v

namespace MvPolynomial

open Set Function Finsupp

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

section PDeriv

variable [CommSemiring R]

def pderiv (i : σ) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  letI := Classical.decEq σ
  mkDerivation R <| Pi.single i 1

theorem pderiv_def [DecidableEq σ] (i : σ) : pderiv i = mkDerivation R (Pi.single i 1) := by
  unfold pderiv; congr!
