/-
Extracted from Algebra/Polynomial/EraseLead.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `eraseLead f`: the polynomial `f - leading term of f`

`eraseLead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/

noncomputable section

open Polynomial

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

def eraseLead (f : R[X]) : R[X] :=
  Polynomial.erase f.natDegree f

section EraseLead

theorem eraseLead_support (f : R[X]) : f.eraseLead.support = f.support.erase f.natDegree := by
  simp only [eraseLead, support_erase]

theorem eraseLead_coeff (i : ℕ) :
    f.eraseLead.coeff i = if i = f.natDegree then 0 else f.coeff i := by
  simp only [eraseLead, coeff_erase]
