/-
Extracted from NumberTheory/Bernoulli.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, -1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the formula for the sums of $k$th
powers. They are related to the Taylor series expansions of $x/\tan(x)$ and
of $\coth(x)$, and also show up in the values that the Riemann Zeta function
takes both at both negative and positive integers (and hence in the
theory of modular forms). For example, if $1 \leq n$ then

$$\zeta(2n)=\sum_{t\geq1}t^{-2n}=(-1)^{n+1}\frac{(2\pi)^{2n}B_{2n}}{2(2n)!}.$$

This result is formalised in Lean: `riemannZeta_two_mul_nat`.

The Bernoulli numbers can be formally defined using the power series

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* and need not concern the mathematician).

Note that $B_1=-1/2$, meaning that we are using the $B_n^-$ of
[from Wikipedia](https://en.wikipedia.org/wiki/Bernoulli_number).

## Implementation detail

The Bernoulli numbers are defined using well-founded induction, by the formula
$$B_n=1-\sum_{k\lt n}\frac{\binom{n}{k}}{n-k+1}B_k.$$
This formula is true for all $n$ and in particular $B_0=1$. Note that this is the definition
for positive Bernoulli numbers, which we call `bernoulli'`. The negative Bernoulli numbers are
then defined as `bernoulli := (-1)^n * bernoulli'`.

## Main theorems

`sum_bernoulli : ∑ k ∈ Finset.range n, (n.choose k : ℚ) * bernoulli k = if n = 1 then 1 else 0`
-/

open Nat Finset Finset.Nat PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-! ### Definitions -/

def bernoulli' (n : ℕ) : ℚ :=
  1 - ∑ k : Fin n, n.choose k / (n - k + 1) * bernoulli' k

theorem bernoulli'_def' (n : ℕ) :
    bernoulli' n = 1 - ∑ k : Fin n, n.choose k / (n - k + 1) * bernoulli' k := by
  rw [bernoulli']

theorem bernoulli'_def (n : ℕ) :
    bernoulli' n = 1 - ∑ k ∈ range n, n.choose k / (n - k + 1) * bernoulli' k := by
  rw [bernoulli'_def', ← Fin.sum_univ_eq_sum_range]

theorem bernoulli'_spec (n : ℕ) :
    (∑ k ∈ range n.succ, (n.choose (n - k) : ℚ) / (n - k + 1) * bernoulli' k) = 1 := by
  rw [sum_range_succ_comm, bernoulli'_def n, tsub_self, choose_zero_right, sub_self, zero_add,
    div_one, cast_one, one_mul, sub_add, ← sum_sub_distrib, ← sub_eq_zero, sub_sub_cancel_left,
    neg_eq_zero]
  exact Finset.sum_eq_zero (fun x hx => by rw [choose_symm (le_of_lt (mem_range.1 hx)), sub_self])

theorem bernoulli'_spec' (n : ℕ) :
    (∑ k ∈ antidiagonal n, ((k.1 + k.2).choose k.2 : ℚ) / (k.2 + 1) * bernoulli' k.1) = 1 := by
  refine ((sum_antidiagonal_eq_sum_range_succ_mk _ n).trans ?_).trans (bernoulli'_spec n)
  refine sum_congr rfl fun x hx => ?_
  simp only [add_tsub_cancel_of_le, mem_range_succ_iff.mp hx, cast_sub]

/-! ### Examples -/

section Examples
