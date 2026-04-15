/-
Extracted from RingTheory/Polynomial/GaussNorm.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gauss norm for polynomials
This file defines the Gauss norm for polynomials. Given a polynomial `p` in `R[X]`, a function
`v : R → ℝ` and a real number `c`, the Gauss norm is defined as the supremum of the set of all
values of `v (p.coeff i) * c ^ i` for all `i` in the support of `p`.

This is mostly useful when `v` is an absolute value on `R` and `c` is set to be `1`, in which case
the Gauss norm corresponds to the maximum of the absolute values of the coefficients of `p`. When
`R` is a subring of `ℂ` and `v` is the standard absolute value, this is sometimes called the
"height" of `p`.

In the file `Mathlib/RingTheory/PowerSeries/GaussNorm.lean`, the Gauss norm is defined for power
series. This is a generalization of the Gauss norm defined in this file in case `v` is a
nonnegative function with `v 0 = 0` and `c ≥ 0`.

## Main Definitions and Results
* `Polynomial.gaussNorm` is the supremum of the set of all values of `v (p.coeff i) * c ^ i`
  for all `i` in the support of `p`, where `p` is a polynomial in `R[X]`, `v : R → ℝ` is a function
  and `c` is a real number.
* `Polynomial.gaussNorm_coe_powerSeries`: if `v` is a nonnegative function with `v 0 = 0` and `c`
  is nonnegative, the Gauss norm of a polynomial is equal to its Gauss norm as a power series.
* `Polynomial.exists_min_eq_gaussNorm`: if `v` is a nonnegative function with `v 0 = 0` and `c`
  is nonnegative, there exists a minimal index `i` such that the Gauss norm of `p` at `c` is
  attained at `i`.
* `Polynomial.isNonarchimedean_gaussNorm`: if `v` is a nonnegative nonarchimedean function with
  `v 0 = 0` and `c` is nonnegative, the Gauss norm is nonarchimedean.
* `Polynomial.gaussNorm_mul`: if `v` is a nonarchimedean absolute value, then the Gauss norm is
  multiplicative.
* `Polynomial.gaussNorm_isAbsoluteValue`: if `v` is a nonarchimedean absolute value, then the
  Gauss norm is an absolute value.
-/

variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ)

namespace Polynomial

variable (p : R[X])

def gaussNorm : ℝ := if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (v (p.coeff i) * c ^ i) else 0
