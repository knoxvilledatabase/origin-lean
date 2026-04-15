/-
Extracted from RingTheory/Polynomial/Cyclotomic/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cyclotomic polynomials.

For `n : ℕ` and an integral domain `R`, we define a modified version of the `n`-th cyclotomic
polynomial with coefficients in `R`, denoted `cyclotomic' n R`, as `∏ (X - μ)`, where `μ` varies
over the primitive `n`th roots of unity. If there is a primitive `n`th root of unity in `R` then
this is the standard definition. We then define the standard cyclotomic polynomial `cyclotomic n R`
with coefficients in any ring `R`.

## Main definition

* `cyclotomic n R` : the `n`-th cyclotomic polynomial with coefficients in `R`.

## Main results

* `Polynomial.degree_cyclotomic` : The degree of `cyclotomic n` is `totient n`.
* `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` : `X ^ n - 1 = ∏ (cyclotomic i)`, where `i`
  divides `n`.
* `Polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius` : The Möbius inversion formula for
  `cyclotomic n R` over an abstract fraction field for `R[X]`.

## Implementation details

Our definition of `cyclotomic' n R` makes sense in any integral domain `R`, but the interesting
results hold if there is a primitive `n`-th root of unity in `R`. In particular, our definition is
not the standard one unless there is a primitive `n`th root of unity in `R`. For example,
`cyclotomic' 3 ℤ = 1`, since there are no primitive cube roots of unity in `ℤ`. The main example is
`R = ℂ`, we decided to work in general since the difficulties are essentially the same.
To get the standard cyclotomic polynomials, we use `unique_int_coeff_of_cycl`, with `R = ℂ`,
to get a polynomial with integer coefficients and then we map it to `R[X]`, for any ring `R`.
-/

open scoped Polynomial

noncomputable section

universe u

namespace Polynomial

section Cyclotomic'

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R]

def cyclotomic' (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : R[X] :=
  ∏ μ ∈ primitiveRoots n R, (X - C μ)
