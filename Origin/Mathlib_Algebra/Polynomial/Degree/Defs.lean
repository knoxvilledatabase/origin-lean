/-
Extracted from Algebra/Polynomial/Degree/Defs.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Degree of univariate polynomials

## Main definitions

* `Polynomial.degree`: the degree of a polynomial, where `0` has degree `⊥`
* `Polynomial.natDegree`: the degree of a polynomial, where `0` has degree `0`
* `Polynomial.leadingCoeff`: the leading coefficient of a polynomial
* `Polynomial.Monic`: a polynomial is monic if its leading coefficient is 0
* `Polynomial.nextCoeff`: the next coefficient after the leading coefficient

## Main results

* `Polynomial.degree_eq_natDegree`: the degree and natDegree coincide for nonzero polynomials
-/

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

def degree (p : R[X]) : WithBot ℕ :=
  p.support.max

def natDegree (p : R[X]) : ℕ :=
  (degree p).unbotD 0

def leadingCoeff (p : R[X]) : R :=
  coeff p (natDegree p)

def Monic (p : R[X]) :=
  leadingCoeff p = (1 : R)

-- INSTANCE (free from Core): Monic.decidable
