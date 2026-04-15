/-
Extracted from RingTheory/MvPowerSeries/Order.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-! # Order of multivariate power series

We work with `MvPowerSeries σ R`, for `Semiring R`, and `w : σ → ℕ`.

## Weighted Order

- `MvPowerSeries.weightedOrder`: the weighted order of a multivariate power series,
  with respect to `w`, as an element of `ℕ∞`.

- `MvPowerSeries.weightedOrder_zero`: the weighted order of `0` is `0`.

- `MvPowerSeries.ne_zero_iff_weightedOrder_finite`: a multivariate power series is nonzero if
  and only if its weighted order is finite.

- `MvPowerSeries.exists_coeff_ne_zero_of_weightedOrder`: if the weighted order is finite,
  then there exists a nonzero coefficient of weight the weighted order.

- `MvPowerSeries.weightedOrder_le` : if a coefficient is nonzero, then the weighted order is at
  most the weight of that exponent.

- `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`: all coefficients of weights strictly less
  than the weighted order vanish.

- `MvPowerSeries.weightedOrder_eq_top_iff`: the weighted order of `f` is `⊤` if and only if `f = 0`.

- `MvPowerSeries.nat_le_weightedOrder`: if all coefficients of weight `< n` vanish, then the
  weighted order is at least `n`.

- `MvPowerSeries.weightedOrder_eq_nat_iff`: the weighted order is some integer `n` iff there
  exists a nonzero coefficient of weight `n`, and all coefficients of strictly smaller weight
  vanish.

- `MvPowerSeries.weightedOrder_monomial`, `MvPowerSeries.weightedOrder_monomial_of_ne_zero`:
  the weighted order of a monomial, of a monomial with nonzero coefficient.

- `MvPowerSeries.min_weightedOrder_le_add`: the order of the sum of two multivariate power series
  is at least the minimum of their orders.

- `MvPowerSeries.weightedOrder_add_of_weightedOrder_ne`: the `weightedOrder` of the sum of two
  formal power series is the minimum of their orders if their orders differ.

- `MvPowerSeries.le_weightedOrder_mul`: the `weightedOrder` of the product of two formal power
  series is at least the sum of their orders.

- `MvPowerSeries.coeff_mul_left_one_sub_of_lt_weightedOrder`,
  `MvPowerSeries.coeff_mul_right_one_sub_of_lt_weightedOrder`: the coefficients of `f * (1 - g)`
  and `(1 - g) * f` in weights strictly less than the weighted order of `g`.

- `MvPowerSeries.coeff_mul_prod_one_sub_of_lt_weightedOrder`: the coefficients of
  `f * Π i in s, (1 - g i)`, in weights strictly less than the weighted orders of `g i`, for
  `i ∈ s`.

## Order

- `MvPowerSeries.order`: the weighted order, for `w = (1 : σ → ℕ)`.

- `MvPowerSeries.ne_zero_iff_order_finite`: `f` is nonzero iff its order is finite.

- `MvPowerSeries.order_eq_top_iff`: the order of `f` is infinite iff `f = 0`.

- `MvPowerSeries.exists_coeff_ne_zero_of_order`: if the order is finite, then there exists a
  nonzero coefficient of degree equal to the order.

- `MvPowerSeries.order_le` : if a coefficient of some degree is nonzero, then the order
  is at least that degree.

- `MvPowerSeries.nat_le_order`: if all coefficients of degree strictly smaller than some integer
  vanish, then the order is at least that integer.

- `MvPowerSeries.order_eq_nat_iff`:  the order of a power series is an integer `n` iff there exists
  a nonzero coefficient in that degree, and all coefficients below that degree vanish.

- `MvPowerSeries.order_monomial`, `MvPowerSeries.order_monomial_of_ne_zero`: the order of a
  monomial, with a nonzero coefficient

- `MvPowerSeries.min_order_le_add`: the order of a sum of two power series is at least the minimum
  of their orders.

- `MvPowerSeries.order_add_of_order_ne`: the order of a sum of two power series of distinct orders
  is the minimum of their orders.

- `MvPowerSeries.order_mul_ge`: the order of a product of two power series is at least the sum of
  their orders.

- `MvPowerSeries.coeff_mul_left_one_sub_of_lt_order`,
  `MvPowerSeries.coeff_mul_right_one_sub_of_lt_order`: the coefficients of `f * (1 - g)` and
  `(1 - g) * f` below the order of `g` coincide with that of `f`.

- `MvPowerSeries.coeff_mul_prod_one_sub_of_lt_order`: the coefficients of `f * Π i in s, (1 - g i)`
  coincide with that of `f` below the minimum of the orders of the `g i`, for `i ∈ s`.

## Homogeneous components

- `MvPowerSeries.weightedHomogeneousComponent`, `MvPowerSeries.homogeneousComponent`: the power
  series which is the sum of all monomials of given weighted degree, resp. degree.

NOTE:
Under `Finite σ`, one can use `Finsupp.finite_of_degree_le` and `Finsupp.finite_of_weight_le` to
show that they have finite support, hence correspond to `MvPolynomial`.

However, when `σ` is finite, this is not necessarily an `MvPolynomial`.
(For example: the homogeneous components of degree 1 of the multivariate power
series, all of which coefficients are `1`, is the sum of all indeterminates.)

TODO: Define a coercion to MvPolynomial.

-/

namespace MvPowerSeries

noncomputable section

open ENat WithTop Finsupp

variable {σ R : Type*} [Semiring R]

section WeightedOrder

variable (w : σ → ℕ) {f g : MvPowerSeries σ R}

-- DISSOLVED: ne_zero_iff_exists_coeff_ne_zero_and_weight

def weightedOrder (f : MvPowerSeries σ R) : ℕ∞ := by
  classical
  exact dite (f = 0) (fun _ => ⊤) fun h =>
    Nat.find ((ne_zero_iff_exists_coeff_ne_zero_and_weight w).mp h)
