/-
Extracted from Algebra/Polynomial/Smeval.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Scalar-multiple polynomial evaluation

This file defines polynomial evaluation via scalar multiplication.  Our polynomials have
coefficients in a semiring `R`, and we evaluate at a weak form of `R`-algebra, namely an additive
commutative monoid with an action of `R` and a notion of natural number power.  This
is a generalization of `Algebra.Polynomial.Eval`.

## Main definitions

* `Polynomial.smeval`: function for evaluating a polynomial with coefficients in a `Semiring`
  `R` at an element `x` of an `AddCommMonoid` `S` that has natural number powers and an `R`-action.
* `smeval.linearMap`: the `smeval` function as an `R`-linear map, when `S` is an `R`-module.
* `smeval.algebraMap`: the `smeval` function as an `R`-algebra map, when `S` is an `R`-algebra.

## Main results

* `smeval_monomial`: monomials evaluate as we expect.
* `smeval_add`, `smeval_smul`: linearity of evaluation, given an `R`-module.
* `smeval_mul`, `smeval_comp`: multiplicativity of evaluation, given power-associativity.
* `eval₂_smulOneHom_eq_smeval`, `leval_eq_smeval.linearMap`,
  `aeval_eq_smeval`, etc.: comparisons

## TODO

* `smeval_neg` and `smeval_intCast` for `R` a ring and `S` an `AddCommGroup`.
* Nonunital evaluation for polynomials with vanishing constant term for `Pow S ℕ+` (different file?)

-/

namespace Polynomial

section MulActionWithZero

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

def smul_pow : ℕ → R → S := fun n r => r • x ^ n

irreducible_def smeval : S := p.sum (smul_pow x)

theorem smeval_eq_sum : p.smeval x = p.sum (smul_pow x) := by rw [smeval_def]
