/-
Extracted from Analysis/SumOverResidueClass.lean
Genuine: 1 of 7 | Dissolved: 6 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.ENNReal

/-!
# Sums over residue classes

We consider infinite sums over functions `f` on `ℕ`, restricted to a residue class mod `m`.

The main result is `summable_indicator_mod_iff`, which states that when `f : ℕ → ℝ` is
decreasing, then the sum over `f` restricted to any residue class
mod `m ≠ 0` converges if and only if the sum over all of `ℕ` converges.
-/

-- DISSOLVED: Finset.sum_indicator_mod

open Set in

-- DISSOLVED: summable_indicator_mod_iff_summable

lemma not_summable_of_antitone_of_neg {f : ℕ → ℝ} (hf : Antitone f) {n : ℕ} (hn : f n < 0) :
    ¬ Summable f := by
  intro hs
  have := hs.tendsto_atTop_zero
  simp only [Metric.tendsto_atTop, dist_zero_right, Real.norm_eq_abs] at this
  obtain ⟨N, hN⟩ := this (|f n|) (abs_pos_of_neg hn)
  specialize hN (max n N) (n.le_max_right N)
  contrapose! hN; clear hN
  have H : f (max n N) ≤ f n := hf (n.le_max_left N)
  rwa [abs_of_neg hn, abs_of_neg (H.trans_lt hn), neg_le_neg_iff]

-- DISSOLVED: not_summable_indicator_mod_of_antitone_of_neg

-- DISSOLVED: summable_indicator_mod_iff_summable_indicator_mod

-- DISSOLVED: summable_indicator_mod_iff

open ZMod

-- DISSOLVED: Nat.sumByResidueClasses
