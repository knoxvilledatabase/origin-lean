/-
Extracted from Algebra/Polynomial/CancelLeads.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cancel the leading terms of two polynomials

## Definition

* `cancelLeads p q`: the polynomial formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting.

## Main Results
The degree of `cancelLeads` is less than that of the larger of the two polynomials being cancelled.
Thus it is useful for induction or minimal-degree arguments.
-/

namespace Polynomial

noncomputable section

open Polynomial

variable {R : Type*}

section Ring

variable [Ring R] (p q : R[X])

def cancelLeads : R[X] :=
  C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q -
    C q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p

variable {p q}
