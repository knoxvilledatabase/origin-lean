/-
Extracted from Analysis/SpecialFunctions/ArithmeticGeometricMean.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The arithmetic-geometric mean

Starting with two nonnegative real numbers, repeatedly replace them with their arithmetic and
geometric means. By the AM-GM inequality, the smaller number (geometric mean) will monotonically
increase and the larger number (arithmetic mean) will monotonically decrease.

The two monotone sequences converge to the same limit – the arithmetic-geometric mean (AGM).
This file defines the AGM in the `NNReal` namespace and proves some of its basic properties.

## References

* https://en.wikipedia.org/wiki/Arithmetic–geometric_mean
-/

namespace NNReal

lemma sqrt_mul_le_half_add (x y : ℝ≥0) : sqrt (x * y) ≤ (x + y) / 2 := by
  rw [sqrt_le_iff_le_sq, div_pow, le_div_iff₀' (by positivity), ← mul_assoc]
  norm_num
  exact four_mul_le_sq_add ..

lemma sqrt_mul_lt_half_add_of_ne {x y : ℝ≥0} (h : x ≠ y) : sqrt (x * y) < (x + y) / 2 := by
  wlog hl : y < x generalizing x y
  · specialize this h.symm (h.gt_or_lt.resolve_left hl)
    rwa [mul_comm, add_comm]
  have key : 0 < (x - y) ^ 2 := sq_pos_iff.mpr (by rwa [← zero_lt_iff, tsub_pos_iff_lt])
  rw [sq, tsub_mul, mul_tsub, mul_tsub, tsub_tsub_eq_add_tsub_of_le (by gcongr),
    tsub_add_eq_add_tsub (by gcongr), tsub_tsub, show x * y + y * x = 2 * x * y by ring,
    tsub_pos_iff_lt, ← sq, ← sq] at key
  rw [← sqrt_sq (_ / 2), sqrt_lt_sqrt, div_pow, lt_div_iff₀' (by positivity),
    show (2 : ℝ≥0) ^ 2 * (x * y) = 2 * x * y + 2 * x * y by ring, add_sq, add_right_comm]
  gcongr

open Function Filter Topology

noncomputable def agmSequences (x y : ℝ≥0) : ℕ → ℝ≥0 × ℝ≥0 :=
  fun n ↦ (fun p ↦ (sqrt (p.1 * p.2), (p.1 + p.2) / 2))^[n + 1] (x, y)

variable {x y : ℝ≥0} {n : ℕ}
