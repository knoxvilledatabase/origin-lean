/-
Extracted from NumberTheory/ZetaValues.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Critical values of the Riemann zeta function

In this file we prove formulae for the critical values of `ζ(s)`, and more generally of Hurwitz
zeta functions, in terms of Bernoulli polynomials.

## Main results:

* `hasSum_zeta_nat`: the final formula for zeta values,
  $$\zeta(2k) = \frac{(-1)^{(k + 1)} 2 ^ {2k - 1} \pi^{2k} B_{2 k}}{(2 k)!}.$$
* `hasSum_zeta_two` and `hasSum_zeta_four`: special cases given explicitly.
* `hasSum_one_div_nat_pow_mul_cos`: a formula for the sum `∑ (n : ℕ), cos (2 π i n x) / n ^ k` as
  an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 2` even.
* `hasSum_one_div_nat_pow_mul_sin`: a formula for the sum `∑ (n : ℕ), sin (2 π i n x) / n ^ k` as
  an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 3` odd.
-/

noncomputable section

open scoped Nat Real Interval

open Complex MeasureTheory Set intervalIntegral

local notation "𝕌" => UnitAddCircle

section BernoulliFunProps

/-! Simple properties of the Bernoulli polynomial, as a function `ℝ → ℝ`. -/

def bernoulliFun (k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli k)).eval x

section Evaluation
