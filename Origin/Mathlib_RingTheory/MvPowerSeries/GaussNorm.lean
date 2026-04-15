/-
Extracted from RingTheory/MvPowerSeries/GaussNorm.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gauss norm for multivariate power series

This file defines the Gauss norm for power series. Given a multivariate power series `f`, a
function `v : R → ℝ` and a tuple `c` of real numbers, the Gauss norm is defined as the supremum of
the set of all values of `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`.

## Main definitions and results

* `MvPowerSeries.gaussNormC` is the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`, where `f` is a multivariate power
  series, `v : R → ℝ` is a function and `c` is a tuple of real numbers.

* `MvPowerSeries.gaussNormC_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.

* `MvPowerSeries.gaussNormC_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0`
  for all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series
  is zero.

* `MvPowerSeries.gaussNorm_add_le_max`: if `v` is a non-negative non-archimedean function and the
  set of values `v (coeff t f) * ∏ i : t.support, c i` is bounded above (similarily for `g`), then
  the Gauss norm has the non-archimedean property.
-/

namespace MvPowerSeries

variable {R σ : Type*} [Semiring R] (v : R → ℝ) (c : σ → ℝ) (f : MvPowerSeries σ R)

noncomputable def gaussNorm : ℝ :=
   ⨆ t : σ →₀ ℕ, v (coeff t f) * t.prod (c · ^ ·)

abbrev HasGaussNorm := BddAbove (Set.range (fun (t : σ →₀ ℕ) ↦ (v (coeff t f) * t.prod (c · ^ ·))))
