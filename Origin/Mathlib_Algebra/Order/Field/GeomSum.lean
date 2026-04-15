/-
Extracted from Algebra/Order/Field/GeomSum.lean
Genuine: 5 of 6 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Partial sums of geometric series in an ordered field

This file upper- and lower-bounds the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof.
-/

variable {K : Type*}

open Finset MulOpposite

section Semifield

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [CanonicallyOrderedAdd K]
  [Sub K] [OrderedSub K] {x y : K}

lemma geom₂_sum_of_gt (h : y < x) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_ge h.le n)

lemma geom₂_sum_of_lt (h : x < y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (y ^ n - x ^ n) / (y - x) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_le h.le n)

lemma geom_sum_of_one_lt (h : 1 < x) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (x ^ n - 1) / (x - 1) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_one_le h.le n)

lemma geom_sum_of_lt_one (h : x < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (1 - x ^ n) / (1 - x) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_le_one h.le n)

-- DISSOLVED: geom_sum_lt

end Semifield

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {x : K} {m n : ℕ}

lemma geom_sum_Ico_le_of_lt_one (hx : 0 ≤ x) (h'x : x < 1) :
    ∑ i ∈ Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  rcases le_or_gt m n with (hmn | hmn)
  · rw [geom_sum_Ico' h'x.ne hmn]
    apply div_le_div₀ (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    simpa using pow_nonneg hx _
  · rw [Ico_eq_empty, sum_empty]
    · apply div_nonneg (pow_nonneg hx _)
      simpa using h'x.le
    · simpa using hmn.le
