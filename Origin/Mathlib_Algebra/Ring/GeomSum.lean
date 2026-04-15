/-
Extracted from Algebra/Ring/GeomSum.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Partial sums of geometric series in a ring

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof.

Several variants are recorded, generalising in particular to the case of a noncommutative ring in
which `x` and `y` commute. Even versions not using division or subtraction, valid in each semiring,
are recorded.
-/

assert_not_exists Field IsOrderedRing

open Finset MulOpposite

variable {R S : Type*}

section Semiring

variable [Semiring R] [Semiring S] {x y : R}

lemma geom_sum_succ {x : R} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = (x * ∑ i ∈ range n, x ^ i) + 1 := by
  simp only [mul_sum, ← pow_succ', sum_range_succ', pow_zero]

lemma geom_sum_succ' {x : R} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = x ^ n + ∑ i ∈ range n, x ^ i :=
  (sum_range_succ _ _).trans (add_comm _ _)
