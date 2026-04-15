/-
Extracted from Algebra/Polynomial/SumIteratedDerivative.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sum of iterated derivatives

This file introduces `Polynomial.sumIDeriv`, the sum of the iterated derivatives of a polynomial,
as a linear map. This is used in particular in the proof of the Lindemann-Weierstrass theorem
(see https://github.com/leanprover-community/mathlib4/pull/6718).

## Main results

* `Polynomial.sumIDeriv`: Sum of iterated derivatives of a polynomial, as a linear map
* `Polynomial.sumIDeriv_apply`, `Polynomial.sumIDeriv_apply_of_lt`,
  `Polynomial.sumIDeriv_apply_of_le`: `Polynomial.sumIDeriv` expressed as a sum
* `Polynomial.sumIDeriv_C`, `Polynomial.sumIDeriv_X`: `Polynomial.sumIDeriv` applied to simple
  polynomials
* `Polynomial.sumIDeriv_map`: `Polynomial.sumIDeriv` commutes with `Polynomial.map`
* `Polynomial.sumIDeriv_derivative`: `Polynomial.sumIDeriv` commutes with `Polynomial.derivative`
* `Polynomial.sumIDeriv_eq_self_add`: `sumIDeriv p = p + derivative (sumIDeriv p)`
* `Polynomial.exists_iterate_derivative_eq_factorial_smul`: the `k`-th iterated derivative of a
  polynomial has a common factor `k!`
* `Polynomial.aeval_iterate_derivative_of_lt`, `Polynomial.aeval_iterate_derivative_self`,
  `Polynomial.aeval_iterate_derivative_of_ge`: applying `Polynomial.aeval` to iterated derivatives
* `Polynomial.aeval_sumIDeriv`, `Polynomial.aeval_sumIDeriv_of_pos`: applying `Polynomial.aeval` to
  `Polynomial.sumIDeriv`

-/

open Finset

open scoped Nat

namespace Polynomial

variable {R S : Type*}

section Semiring

variable [Semiring R] [Semiring S]

noncomputable def sumIDeriv : R[X] →ₗ[R] R[X] :=
  Finsupp.lsum ℕ (fun _ ↦ LinearMap.id) ∘ₗ derivativeFinsupp

theorem sumIDeriv_apply (p : R[X]) :
    sumIDeriv p = ∑ i ∈ range (p.natDegree + 1), derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp) _ (by simp)

theorem sumIDeriv_apply_of_lt {p : R[X]} {n : ℕ} (hn : p.natDegree < n) :
    sumIDeriv p = ∑ i ∈ range n, derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

theorem sumIDeriv_apply_of_le {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    sumIDeriv p = ∑ i ∈ range (n + 1), derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)
