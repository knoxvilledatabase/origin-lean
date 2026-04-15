/-
Extracted from Algebra/Polynomial/HasseDeriv.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Hasse derivative of polynomials

The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It is a variant of the usual derivative, and satisfies `k! * (hasseDeriv k f) = derivative^[k] f`.
The main benefit is that is gives an atomic way of talking about expressions such as
`(derivative^[k] f).eval r / k!`, that occur in Taylor expansions, for example.

## Main declarations

In the following, we write `D k` for the `k`-th Hasse derivative `hasse_deriv k`.

* `Polynomial.hasseDeriv`: the `k`-th Hasse derivative of a polynomial
* `Polynomial.hasseDeriv_zero`: the `0`th Hasse derivative is the identity
* `Polynomial.hasseDeriv_one`: the `1`st Hasse derivative is the usual derivative
* `Polynomial.factorial_smul_hasseDeriv`: the identity `k! • (D k f) = derivative^[k] f`
* `Polynomial.hasseDeriv_comp`: the identity `(D k).comp (D l) = (k+l).choose k • D (k+l)`
* `Polynomial.hasseDeriv_mul`:
  the "Leibniz rule" `D k (f * g) = ∑ ij ∈ antidiagonal k, D ij.1 f * D ij.2 g`

For the identity principle, see `Polynomial.eq_zero_of_hasseDeriv_eq_zero`
in `Mathlib/Algebra/Polynomial/Taylor.lean`.

## Reference

https://math.fontein.de/2009/08/12/the-hasse-derivative/

-/

noncomputable section

namespace Polynomial

open Nat Polynomial

open Function

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

def hasseDeriv (k : ℕ) : R[X] →ₗ[R] R[X] :=
  lsum fun i => monomial (i - k) ∘ₗ DistribSMul.toLinearMap R R (i.choose k)

theorem hasseDeriv_apply :
    hasseDeriv k f = f.sum fun i r => monomial (i - k) (↑(i.choose k) * r) := by
  dsimp [hasseDeriv]
  simp

theorem hasseDeriv_coeff (n : ℕ) :
    (hasseDeriv k f).coeff n = (n + k).choose k * f.coeff (n + k) := by
  rw [hasseDeriv_apply, coeff_sum, sum_def, Finset.sum_eq_single (n + k), coeff_monomial]
  · simp
  · #adaptation_note
    /-- Prior to nightly-2025-08-14, this was working as
    `grind [coeff_monomial, Nat.choose_eq_zero_of_lt, Nat.cast_zero, zero_mul]` -/
    intro i _hi hink
    rw [coeff_monomial]
    by_cases hik : i < k
    · simp only [Nat.choose_eq_zero_of_lt hik, ite_self, Nat.cast_zero, zero_mul]
    · grind
  · intro h
    simp only [notMem_support_iff.mp h, monomial_zero_right, mul_zero, coeff_zero]

theorem hasseDeriv_zero' : hasseDeriv 0 f = f := by
  simp only [hasseDeriv_apply, Nat.sub_zero, choose_zero_right, cast_one, one_mul, sum_monomial_eq]
