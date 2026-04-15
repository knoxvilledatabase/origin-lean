/-
Extracted from NumberTheory/Harmonic/Defs.lean
Genuine: 3 | Conflates: 0 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity

/-!

This file defines the harmonic numbers.

* `Mathilb/NumberTheory/Harmonic/Int.lean` proves that the `n`th harmonic number is not an integer.
* `Mathlib/NumberTheory/Harmonic/Bounds.lean` provides basic log bounds.

-/

def harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹

@[simp]
lemma harmonic_zero : harmonic 0 = 0 :=
  rfl

@[simp]
lemma harmonic_succ (n : ℕ) : harmonic (n + 1) = harmonic n + (↑(n + 1))⁻¹ :=
  Finset.sum_range_succ ..

-- DISSOLVED: harmonic_pos

lemma harmonic_eq_sum_Icc {n : ℕ} :  harmonic n = ∑ i ∈ Finset.Icc 1 n, (↑i)⁻¹ := by
  rw [harmonic, Finset.range_eq_Ico, Finset.sum_Ico_add' (fun (i : ℕ) ↦ (i : ℚ)⁻¹) 0 n (c := 1)]
  -- It might be better to restate `Nat.Ico_succ_right` in terms of `+ 1`,
  -- as we try to move away from `Nat.succ`.
  simp only [Nat.add_one, Nat.Ico_succ_right]
