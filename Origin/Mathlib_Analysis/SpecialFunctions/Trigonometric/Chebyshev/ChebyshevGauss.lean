/-
Extracted from Analysis/SpecialFunctions/Trigonometric/Chebyshev/ChebyshevGauss.lean
Genuine: 1 of 3 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chebyshev polynomials over the reals: Chebyshev–Gauss

The Chebyshev–Gauss property calculates an integral of a polynomial of degree `< 2 * n`
with respect to the weight function `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` by a sum
over appropriate evaluations of the polynomial.

## Main statements

* integral_eq_sumZeroes: The integral of a polynomial of degree `< 2 * n` with respect to the weight
  function `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` is equal to `π` times the average of its values
  on the points `cos ((2 * i + 1) / (2 * n) * π)` for `0 ≤ i < n`.

## Implementation

The statement is proved for Chebyshev polynomials using the complex exponential representation
of `cos`, and then deduced for arbitrary polynomials.
-/

namespace Polynomial.Chebyshev

open Real Polynomial Finset

open Complex (exp I)

-- DISSOLVED: exp_sub_one_ne_zero

-- DISSOLVED: sum_exp

noncomputable def sumZeroes (n : ℕ) (P : ℝ[X]) : ℝ :=
    (π / n) * ∑ i ∈ range n, P.eval (cos ((2 * i + 1) / (2 * n) * π))
