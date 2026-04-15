/-
Extracted from Algebra/Field/GeomSum.lean
Genuine: 7 of 8 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Partial sums of geometric series in a field

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof.

## Main statements

* `geom_sum_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-x^m}{x-1}$ in a division ring.
* `geom_sum₂_Ico` proves that $\sum_{i=m}^{n-1} x^iy^{n - 1 - i}=\frac{x^n-y^{n-m}x^m}{x-y}$
  in a field.

Several variants are recorded, generalising in particular to the case of a division ring in
which `x` and `y` commute.
-/

assert_not_exists IsOrderedRing

variable {R K : Type*}

open Finset MulOpposite

section DivisionRing

variable [DivisionRing K] {x y : K}

protected theorem Commute.geom_sum₂ (h' : Commute x y) (h : x ≠ y)
    (n : ℕ) : ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) := by
  have : x - y ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h'.geom_sum₂_mul, mul_div_cancel_right₀ _ this]

theorem geom_sum_eq (h : x ≠ 1) (n : ℕ) : ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1) := by
  have : x - 1 ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← geom_sum_mul, mul_div_cancel_right₀ _ this]

protected theorem Commute.geom_sum₂_Ico (h : Commute x y) (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) := by
  have : x - y ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h.geom_sum₂_Ico_mul hmn, mul_div_cancel_right₀ _ this]

lemma geom_sum_Ico (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) := by
  simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same, sub_sub_sub_cancel_right]

lemma geom_sum_Ico' (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ m - x ^ n) / (1 - x) := by
  simpa [geom_sum_Ico hx hmn] using neg_div_neg_eq (x ^ m - x ^ n) (1 - x)

-- DISSOLVED: geom_sum_inv

end DivisionRing

section Field

variable [Field K] {x y : K}

lemma geom₂_sum (h : x ≠ y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  (Commute.all x y).geom_sum₂ h n

lemma geom_sum₂_Ico (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) :=
  (Commute.all x y).geom_sum₂_Ico hxy hmn

end Field
