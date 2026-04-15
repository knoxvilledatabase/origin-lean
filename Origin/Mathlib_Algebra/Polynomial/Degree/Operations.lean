/-
Extracted from Algebra/Polynomial/Degree/Operations.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Lemmas for calculating the degree of univariate polynomials

## Main results
- `degree_mul` : The degree of the product is the sum of degrees
- `leadingCoeff_add_of_degree_eq` and `leadingCoeff_add_of_degree_lt` :
    The leading coefficient of a sum is determined by the leading coefficients and degrees
-/

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem supDegree_eq_degree (p : R[X]) : p.toFinsupp.supDegree WithBot.some = p.degree :=
  max_eq_sup_coe

theorem degree_lt_wf : WellFounded fun p q : R[X] => degree p < degree q :=
  InvImage.wf degree wellFounded_lt

-- INSTANCE (free from Core): :
