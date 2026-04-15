/-
Extracted from Probability/ProbabilityMassFunction/Binomial.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The binomial distribution

This file defines the probability mass function of the binomial distribution.

## Main results

* `binomial_one_eq_bernoulli`: For `n = 1`, it is equal to `PMF.bernoulli`.
-/

namespace PMF

open ENNReal NNReal

def binomial (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF (Fin (n + 1)) :=
  .ofFintype (fun i =>
      ↑(p ^ (i : ℕ) * (1 - p) ^ ((Fin.last n - i) : ℕ) * (n.choose i : ℕ))) (by
    dsimp only
    norm_cast
    convert (add_pow p (1 - p) n).symm
    · rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos hi]
    · rw [add_tsub_cancel_of_le (mod_cast h), one_pow])

theorem binomial_apply (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) (i : Fin (n + 1)) :
    binomial p h n i = p ^ (i : ℕ) * (1 - p) ^ ((Fin.last n - i) : ℕ) * (n.choose i : ℕ) := by
  simp [binomial]
