/-
Extracted from NumberTheory/BernoulliPolynomials.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bernoulli polynomials

The [Bernoulli polynomials](https://en.wikipedia.org/wiki/Bernoulli_polynomials)
are an important tool obtained from Bernoulli numbers.

## Mathematical overview

The $n$-th Bernoulli polynomial is defined as
$$ B_n(X) = ∑_{k = 0}^n {n \choose k} (-1)^k B_k X^{n - k} $$
where $B_k$ is the $k$-th Bernoulli number. The Bernoulli polynomials are generating functions,
$$ \frac{t e^{tX} }{ e^t - 1} = ∑_{n = 0}^{\infty} B_n(X) \frac{t^n}{n!} $$

## Implementation detail

Bernoulli polynomials are defined using `bernoulli`, the Bernoulli numbers.

## Main theorems

- `sum_bernoulli`: The sum of the $k^\mathrm{th}$ Bernoulli polynomial with binomial
  coefficients up to `n` is `(n + 1) * X^n`.
- `Polynomial.bernoulli_generating_function`: The Bernoulli polynomials act as generating functions
  for the exponential.

-/

noncomputable section

open Nat Polynomial

open Nat Finset

namespace Polynomial

def bernoulli (n : ℕ) : ℚ[X] :=
  ∑ i ∈ range (n + 1), Polynomial.monomial (n - i) (_root_.bernoulli i * choose n i)

theorem bernoulli_def (n : ℕ) : bernoulli n =
    ∑ i ∈ range (n + 1), Polynomial.monomial i (_root_.bernoulli (n - i) * choose n i) := by
  rw [← sum_range_reflect, add_succ_sub_one, add_zero, bernoulli]
  apply sum_congr rfl
  rintro x hx
  rw [mem_range_succ_iff] at hx
  rw [choose_symm hx, tsub_tsub_cancel_of_le hx]

theorem coeff_bernoulli (n i : ℕ) :
    (bernoulli n).coeff i = if i ≤ n then (_root_.bernoulli (n - i) * choose n i) else 0 := by
  simp only [bernoulli, finset_sum_coeff, coeff_monomial]
  split_ifs with h
  · convert sum_ite_eq_of_mem (range (n + 1)) (n - i) _ (by grind) using 3 <;> grind [choose_symm]
  · exact Finset.sum_eq_zero <| by grind

section Examples
