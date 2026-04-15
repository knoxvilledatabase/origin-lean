/-
Extracted from Analysis/SpecialFunctions/Pochhammer.lean
Genuine: 6 of 9 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pochhammer polynomials

This file proves analysis theorems for Pochhammer polynomials.

## Main statements

* `Differentiable.descPochhammer_eval` is the proof that the descending Pochhammer polynomial
  `descPochhammer ℝ n` is differentiable.

* `ConvexOn.descPochhammer_eval` is the proof that the descending Pochhammer polynomial
  `descPochhammer ℝ n` is convex on `[n-1, ∞)`.

* `descPochhammer_eval_le_sum_descFactorial` is a special case of **Jensen's inequality**
  for `Nat.descFactorial`.

* `descPochhammer_eval_div_factorial_le_sum_choose` is a special case of **Jensen's inequality**
  for `Nat.choose`.
-/

section DescPochhammer

variable {n : ℕ} {𝕜 : Type*} {k : 𝕜} [NontriviallyNormedField 𝕜]

theorem differentiable_descPochhammer_eval : Differentiable 𝕜 (descPochhammer 𝕜 n).eval := by
  simp [descPochhammer_eval_eq_prod_range, Differentiable.fun_finset_prod]

theorem continuous_descPochhammer_eval : Continuous (descPochhammer 𝕜 n).eval := by
  exact differentiable_descPochhammer_eval.continuous

lemma deriv_descPochhammer_eval_eq_sum_prod_range_erase (n : ℕ) (k : 𝕜) :
    deriv (descPochhammer 𝕜 n).eval k
      = ∑ i ∈ Finset.range n, ∏ j ∈ (Finset.range n).erase i, (k - j) := by
  simp [descPochhammer_eval_eq_prod_range, deriv_fun_finset_prod]

lemma monotoneOn_deriv_descPochhammer_eval (n : ℕ) :
    MonotoneOn (deriv (descPochhammer ℝ n).eval) (Set.Ioi (n - 1 : ℝ)) := by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ioi, Nat.cast_add_one, add_sub_cancel_right] at ha hb
    simp_rw [deriv_descPochhammer_eval_eq_sum_prod_range_erase]
    gcongr with i hi
    intro j hj
    rw [Finset.mem_erase, Finset.mem_range] at hj
    apply sub_nonneg_of_le
    exact ha.le.trans' (mod_cast Nat.le_pred_of_lt hj.2)

theorem convexOn_descPochhammer_eval (n : ℕ) :
    ConvexOn ℝ (Set.Ici (n - 1 : ℝ)) (descPochhammer ℝ n).eval := by
  rcases n.eq_zero_or_pos with h_eq | _
  · simp [h_eq, convexOn_const, convex_Ici]
  · apply MonotoneOn.convexOn_of_deriv (convex_Ici (n - 1 : ℝ))
      continuous_descPochhammer_eval.continuousOn
      differentiable_descPochhammer_eval.differentiableOn
    rw [interior_Ici]
    exact monotoneOn_deriv_descPochhammer_eval n

private lemma piecewise_Ici_descPochhammer_eval_zero_eq_descFactorial (k n : ℕ) :
    (Set.Ici (n - 1 : ℝ)).piecewise (descPochhammer ℝ n).eval 0 k
      = k.descFactorial n := by
  rw [Set.piecewise, descPochhammer_eval_eq_descFactorial, ite_eq_left_iff, Set.mem_Ici, not_le,
    eq_comm, Pi.zero_apply, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt, ← @Nat.cast_lt ℝ]
  exact (sub_lt_self (n : ℝ) zero_lt_one).trans'

-- DISSOLVED: convexOn_piecewise_Ici_descPochhammer_eval_zero

-- DISSOLVED: descPochhammer_eval_le_sum_descFactorial

-- DISSOLVED: descPochhammer_eval_div_factorial_le_sum_choose

end DescPochhammer
