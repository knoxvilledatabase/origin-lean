/-
Extracted from Probability/ProbabilityMassFunction/Binomial.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.FinCases

noncomputable section

/-!
# The binomial distribution

This file defines the probability mass function of the binomial distribution.

## Main results

* `binomial_one_eq_bernoulli`: For `n = 1`, it is equal to `PMF.bernoulli`.
-/

namespace PMF

open ENNReal

noncomputable
def binomial (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) : PMF (Fin (n + 1)) :=
  .ofFintype (fun i => p^(i : ℕ) * (1-p)^((Fin.last n - i) : ℕ) * (n.choose i : ℕ)) (by
    convert (add_pow p (1-p) n).symm
    · rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos hi, Fin.last]
    · simp [h])

theorem binomial_apply (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) (i : Fin (n + 1)) :
    binomial p h n i = p^(i : ℕ) * (1-p)^((Fin.last n - i) : ℕ) * (n.choose i : ℕ) := rfl

@[simp]
theorem binomial_apply_zero (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) :
    binomial p h n 0 = (1-p)^n := by
  simp [binomial_apply]

@[simp]
theorem binomial_apply_last (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) :
    binomial p h n (.last n) = p^n := by
  simp [binomial_apply]

theorem binomial_one_eq_bernoulli (p : ℝ≥0∞) (h : p ≤ 1) :
    binomial p h 1 = (bernoulli p h).map (cond · 1 0) := by
  ext i; fin_cases i <;> simp [tsum_bool, binomial_apply]

end PMF
