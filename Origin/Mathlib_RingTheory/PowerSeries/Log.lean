/-
Extracted from RingTheory/PowerSeries/Log.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Logarithmic Power Series

This file defines the logarithmic power series `log A = ∑ (-1)^(n+1)/n · Xⁿ`
over ℚ-algebras and establishes its key properties.

## Main definitions

* `PowerSeries.log`: The power series `log(1+X) = X - X²/2 + X³/3 - ⋯`.

## Main results

* `PowerSeries.coeff_log`: The coefficient of `log A` at `n` is `(-1)^(n+1)/n` for `n ≥ 1`,
  and `0` for `n = 0`.
* `PowerSeries.constantCoeff_log`: The constant term of `log A` is `0`.
* `PowerSeries.map_log`: `log` is preserved by ring homomorphisms between ℚ-algebras.
* `PowerSeries.coeff_one_log`: The coefficient of `log A` at `1` is `1`.
* `PowerSeries.order_log`: The order of `log A` is `1`.
* `PowerSeries.deriv_log`: The derivative of `log(1+X)` is the geometric series
  `∑ (-1)^n · Xⁿ = 1/(1+X)`.
-/

namespace PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

def log : PowerSeries A :=
  mk fun n ↦ if n = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (n + 1) / n)

variable {A}
