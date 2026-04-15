/-
Extracted from RingTheory/MvPolynomial/MonomialOrder.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Degree, leading coefficient and leading term of polynomials with respect to a monomial order

We consider a type `σ` of indeterminates and a commutative semiring `R`
and a monomial order `m : MonomialOrder σ`.

* `m.degree f` is the degree of `f` for the monomial ordering `m`.

* `m.leadingCoeff f` is the leading coefficient of `f` for the monomial ordering `m`.

* `m.Monic f` asserts that the leading coefficient of `f` is `1`.

* `m.leadingTerm f` is the leading term of `f` for the monomial ordering `m`.

* `m.sPolynomial f g` is S-polynomial of `f` and `g`.

* `m.leadingCoeff_ne_zero_iff f` asserts that this coefficient is nonzero iff `f ≠ 0`.

* in a field, `m.isUnit_leadingCoeff f` asserts that this coefficient is a unit iff `f ≠ 0`.

* `m.degree_add_le` : the `m.degree` of `f + g` is smaller than or equal to the supremum
  of those of `f` and `g`.

* `m.degree_add_of_lt h` : the `m.degree` of `f + g` is equal to that of `f`
  if the `m.degree` of `g` is strictly smaller than that `f`.

* `m.leadingCoeff_add_of_lt h`: then, the leading coefficient of `f + g` is that of `f`.

* `m.degree_add_of_ne h` : the `m.degree` of `f + g` is equal to that the supremum
  of those of `f` and `g` if they are distinct.

* `m.degree_sub_le` : the `m.degree` of `f - g` is smaller than or equal to the supremum
  of those of `f` and `g`.

* `m.degree_sub_of_lt h` : the `m.degree` of `f - g` is equal to that of `f`
  if the `m.degree` of `g` is strictly smaller than that `f`.

* `m.leadingCoeff_sub_of_lt h`: then, the leading coefficient of `f - g` is that of `f`.

* `m.degree_mul_le`: the `m.degree` of `f * g` is smaller than or equal to the sum of those of
  `f` and `g`.

* `m.degree_mul_of_mul_leadingCoeff_ne_zero` : if the product of the leading coefficients
  is nonzero, then the degree is the sum of the degrees.

* `m.leadingCoeff_mul_of_mul_leadingCoeff_ne_zero` : if the product of the leading coefficients
  is nonzero, then the leading coefficient is that product.

* `m.degree_mul_of_left_mem_nonZeroDivisors`, `m.degree_mul_of_right_mem_nonZeroDivisors` and
  `m.degree_mul` assert the equality when the leading coefficient of `f` or `g` isn't zero divisors,
  or when `R` is a domain and `f` and `g` are nonzero.

* `m.leadingCoeff_mul_of_left_mem_nonZeroDivisors`,
  `m.leadingCoeff_mul_of_right_mem_nonZeroDivisors`
  and `m.leadingCoeff_mul` say that `m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g`

* `m.degree_pow_of_pow_leadingCoeff_ne_zero` : is the `n`th power of the leading coefficient
  of `f` is nonzero, then the degree of `f ^ n` is `n • (m.degree f)`

* `m.leadingCoeff_pow_of_pow_leadingCoeff_ne_zero` : is the `n`th power of the leading coefficient
  of `f` is nonzero, then the leading coefficient of `f ^ n` is that power.

* `m.degree_prod_of_mem_nonZeroDivisors` : the degree of a product of polynomials whose leading
  coefficients aren't zero divisors is the sum of their degrees.

* `m.leadingCoeff_prod_of_mem_nonZeroDivisors` : the leading coefficient of a product of polynomials
  whose leading coefficients aren't zero divisors is the product of their leading coefficients.

* `m.Monic.prod` : a product of monic polynomials is monic.

* `m.degree_sub_leadingTerm_lt_iff` : the degree of `f - m.leadingTerm f` is smaller than the
  degree of `f` if and only if `m.degree f ≠ 0`.

## Reference

[Becker-Weispfenning1993]

-/

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder nonZeroDivisors

variable {σ : Type*} {m : MonomialOrder σ}

section Semiring

variable {R : Type*} [CommSemiring R]

variable (m) in

noncomputable def degree (f : MvPolynomial σ R) : σ →₀ ℕ :=
  m.toSyn.symm (f.support.sup m.toSyn)

variable (m) in

noncomputable def leadingCoeff (f : MvPolynomial σ R) : R :=
  f.coeff (m.degree f)

variable (m) in

def Monic (f : MvPolynomial σ R) : Prop :=
  m.leadingCoeff f = 1

variable (m) in

noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)
