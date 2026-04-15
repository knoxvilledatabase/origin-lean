/-
Extracted from RingTheory/MvPowerSeries/Trunc.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Formal (multivariate) power series - Truncation

* `MvPowerSeries.truncFinset s p` restricts the support of a multivariate power series `p`
  to a finite set of monomials and obtains a multivariate polynomial.

* `MvPowerSeries.trunc n φ` truncates a formal multivariate power series
  to the multivariate polynomial that has the same coefficients as `φ`,
  for all `m < n`, and `0` otherwise.

  Note that here, `m` and `n` have types `σ →₀ ℕ`,
  so that `m < n` means that `m ≠ n` and `m s ≤ n s` for all `s : σ`.

* `MvPowerSeries.trunc_one` : truncation of the unit power series

* `MvPowerSeries.trunc_C` : truncation of a constant

* `MvPowerSeries.trunc_C_mul` : truncation of constant multiple.

* `MvPowerSeries.trunc' n φ` truncates a formal multivariate power series
  to the multivariate polynomial that has the same coefficients as `φ`,
  for all `m ≤ n`, and `0` otherwise.

  Here, `m` and `n`  have types `σ →₀ ℕ` so that `m ≤ n` means that `m s ≤ n s` for all `s : σ`.


* `MvPowerSeries.coeff_mul_eq_coeff_trunc'_mul_trunc'` : compares the coefficients
  of a product with those of the product of truncations.

* `MvPowerSeries.trunc'_one` : truncation of the unit power series.

* `MvPowerSeries.trunc'_C` : truncation of a constant.

* `MvPowerSeries.trunc'_C_mul` : truncation of a constant multiple.

* `MvPowerSeries.trunc'_map` : image of a truncation under a change of rings

* `MvPowerSeries.truncTotal` : the truncation of a multivariate formal power series at
  a total degree `n` when the index `σ` is finite

-/

noncomputable section

namespace MvPowerSeries

open Finsupp Finset

variable {σ R S : Type*}

section TruncFinset

variable [CommSemiring R] {s : Finset (σ →₀ ℕ)}

def truncFinset (R : Type*) [CommSemiring R] (s : Finset (σ →₀ ℕ)) :
    MvPowerSeries σ R →ₗ[R] MvPolynomial σ R where
  toFun p := ∑ x ∈ s, MvPolynomial.monomial x (p.coeff x)
  map_add' _ _ := by simp [sum_add_distrib]
  map_smul' _ _ := by
    classical
    ext; simp [MvPolynomial.coeff_sum]
