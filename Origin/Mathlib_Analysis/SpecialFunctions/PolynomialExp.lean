/-
Extracted from Analysis/SpecialFunctions/PolynomialExp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Limits of `P(x) / e ^ x` for a polynomial `P`

In this file we prove that $\lim_{x\to\infty}\frac{P(x)}{e^x}=0$ for any polynomial `P`.

## TODO

Add more similar lemmas: limit at `-∞`, versions with $e^{cx}$ etc.

## Keywords

polynomial, limit, exponential
-/

open Filter Topology Real

namespace Polynomial

theorem tendsto_div_exp_atTop (p : ℝ[X]) : Tendsto (fun x ↦ p.eval x / exp x) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | monomial n c => simpa [exp_neg, div_eq_mul_inv, mul_assoc]
    using tendsto_const_nhds.mul (tendsto_pow_mul_exp_neg_atTop_nhds_zero n)
  | add p q hp hq => simpa [add_div] using hp.add hq

end Polynomial
