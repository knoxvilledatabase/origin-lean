/-
Extracted from RingTheory/MvPowerSeries/Trunc.lean
Genuine: 4 of 6 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Interval

/-!

# Formal (multivariate) power series - Truncation

`MvPowerSeries.trunc n φ` truncates a formal multivariate power series
to the multivariate polynomial that has the same coefficients as `φ`,
for all `m < n`, and `0` otherwise.

Note that here, `m` and `n` have types `σ →₀ ℕ`,
so that `m < n` means that `m ≠ n` and `m s ≤ n s` for all `s : σ`.

-/

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

section Trunc

variable [CommSemiring R] (n : σ →₀ ℕ)

def truncFun (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ Finset.Iio n, MvPolynomial.monomial m (coeff R m φ)

theorem coeff_truncFun (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun n φ).coeff m = if m < n then coeff R m φ else 0 := by
  classical
  simp [truncFun, MvPolynomial.coeff_sum]

variable (R)

def trunc : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncFun n
  map_zero' := by
    classical
    ext
    simp [coeff_truncFun]
  map_add' := by
    classical
    intros x y
    ext m
    simp only [coeff_truncFun, MvPolynomial.coeff_add]
    split_ifs
    · rw [map_add]
    · rw [zero_add]

variable {R}

theorem coeff_trunc (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff R m φ else 0 := by
  classical simp [trunc, coeff_truncFun]

-- DISSOLVED: trunc_one

-- DISSOLVED: trunc_c

end Trunc

end MvPowerSeries

end
