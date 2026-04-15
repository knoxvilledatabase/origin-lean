/-
Extracted from Algebra/Order/Ring/Interval.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Intervals of integers in strict ordered rings

These statements could perhaps be generalized, or there could be other variations provided (e.g.,
for `ℕ` instead of `ℤ`, or a version for locally finite `SuccOrder`s with strictly monotone
functions), but for now these are the ones that have found utility in practice (e.g., for lemmas
about `Real.Angle`).
-/

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

lemma IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo
    {r : R} (hr : 0 < r) {k m n : ℤ} (h : r * k ∈ Set.Ioo (r * (m - 1 : ℤ)) (r * (n + 1 : ℤ))) :
    k ∈ Finset.Icc m n := by
  simp only [Set.mem_Ioo, mul_lt_mul_iff_right₀ hr, Int.cast_lt] at h
  grind [Int.lt_iff_add_one_le]

lemma IsStrictOrderedRing.int_eq_of_mul_mem_Ioo
    {r : R} (hr : 0 < r) {k m : ℤ} (h : r * k ∈ Set.Ioo (r * (m - 1 : ℤ)) (r * (m + 1 : ℤ))) :
    k = m := by
  simpa using int_mem_Icc_of_mul_mem_Ioo hr h
