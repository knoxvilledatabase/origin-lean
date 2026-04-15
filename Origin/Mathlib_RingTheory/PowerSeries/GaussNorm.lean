/-
Extracted from RingTheory/PowerSeries/GaussNorm.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gauss norm for power series
This file defines the Gauss norm for power series. Given a power series `f` in `R⟦X⟧`, a function
`v : R → ℝ` and a real number `c`, the Gauss norm is defined as the supremum of the set of all
values of `v (f.coeff i) * c ^ i` for all `i : ℕ`.

In case `f` is a polynomial, `v` is a non-negative function with `v 0 = 0` and `c ≥ 0`,
`f.gaussNorm v c` reduces to the Gauss norm defined in
`Mathlib/RingTheory/Polynomial/GaussNorm.lean`, see `Polynomial.gaussNorm_coe_powerSeries`.

## Main Definitions and Results
* `PowerSeries.gaussNorm` is the supremum of the set of all values of `v (f.coeff i) * c ^ i`
  for all `i : ℕ`, where `f` is a power series in `R⟦X⟧`, `v : R → ℝ` is a function and `c` is a
  real number.
* `PowerSeries.gaussNorm_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.
* `PowerSeries.gaussNorm_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0` for
  all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series is
  zero.

## TODO:
* Set up `gaussNorm` as an abbrev of the MvPowerSeries version from
  Mathlib.RingTheory.MvPowerSeries.GaussNorm
* Refactor to remove the use of FunLike as in MvPowerSeries version
-/

namespace PowerSeries

variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ) (f : R⟦X⟧)

noncomputable def gaussNorm : ℝ := ⨆ i : ℕ, v (f.coeff i) * c ^ i

lemma le_gaussNorm (hbd : BddAbove {x | ∃ i, v (f.coeff i) * c ^ i = x}) (i : ℕ) :
    v (f.coeff i) * c ^ i ≤ f.gaussNorm v c := le_ciSup hbd i
