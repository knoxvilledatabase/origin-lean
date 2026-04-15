/-
Extracted from Analysis/MeanInequalities.lean
Genuine: 31 of 35 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core

/-!
# Mean value inequalities

In this file we prove several inequalities for finite sums, including AM-GM inequality,
HM-GM inequality, Young's inequality, Hölder inequality, and Minkowski inequality. Versions for
integrals of some of these inequalities are available in
`Mathlib/MeasureTheory/Integral/MeanInequalities.lean`.

## Main theorems

### AM-GM inequality:

The inequality says that the geometric mean of a tuple of non-negative numbers is less than or equal
to their arithmetic mean. We prove the weighted version of this inequality: if $w$ and $z$
are two non-negative vectors and $\sum_{i\in s} w_i=1$, then
$$
\prod_{i\in s} z_i^{w_i} ≤ \sum_{i\in s} w_iz_i.
$$
The classical version is a special case of this inequality for $w_i=\frac{1}{n}$.

We prove a few versions of this inequality. Each of the following lemmas comes in two versions:
a version for real-valued non-negative functions is in the `Real` namespace, and a version for
`NNReal`-valued functions is in the `NNReal` namespace.

- `geom_mean_le_arith_mean_weighted` : weighted version for functions on `Finset`s;
- `geom_mean_le_arith_mean2_weighted` : weighted version for two numbers;
- `geom_mean_le_arith_mean3_weighted` : weighted version for three numbers;
- `geom_mean_le_arith_mean4_weighted` : weighted version for four numbers.


### HM-GM inequality:

The inequality says that the harmonic mean of a tuple of positive numbers is less than or equal
to their geometric mean. We prove the weighted version of this inequality: if $w$ and $z$
are two positive vectors and $\sum_{i\in s} w_i=1$, then
$$
1/(\sum_{i\in s} w_i/z_i) ≤ \prod_{i\in s} z_i^{w_i}
$$
The classical version is proven as a special case of this inequality for $w_i=\frac{1}{n}$.

The inequalities are proven only for real-valued positive functions on `Finset`s, and namespaced in
`Real`. The weighted version follows as a corollary of the weighted AM-GM inequality.

### Young's inequality

Young's inequality says that for non-negative numbers `a`, `b`, `p`, `q` such that
$\frac{1}{p}+\frac{1}{q}=1$ we have
$$
ab ≤ \frac{a^p}{p} + \frac{b^q}{q}.
$$

This inequality is a special case of the AM-GM inequality. It is then used to prove Hölder's
inequality (see below).

### Hölder's inequality

The inequality says that for two conjugate exponents `p` and `q` (i.e., for two positive numbers
such that $\frac{1}{p}+\frac{1}{q}=1$) and any two non-negative vectors their inner product is
less than or equal to the product of the $L_p$ norm of the first vector and the $L_q$ norm of the
second vector:
$$
\sum_{i\in s} a_ib_i ≤ \sqrt[p]{\sum_{i\in s} a_i^p}\sqrt[q]{\sum_{i\in s} b_i^q}.
$$

We give versions of this result in `ℝ`, `ℝ≥0` and `ℝ≥0∞`.

There are at least two short proofs of this inequality. In our proof we prenormalize both vectors,
then apply Young's inequality to each $a_ib_i$. Another possible proof would be to deduce this
inequality from the generalized mean inequality for well-chosen vectors and weights.

### Minkowski's inequality

The inequality says that for `p ≥ 1` the function
$$
\|a\|_p=\sqrt[p]{\sum_{i\in s} a_i^p}
$$
satisfies the triangle inequality $\|a+b\|_p\le \|a\|_p+\|b\|_p$.

We give versions of this result in `Real`, `ℝ≥0` and `ℝ≥0∞`.

We deduce this inequality from Hölder's inequality. Namely, Hölder inequality implies that $\|a\|_p$
is the maximum of the inner product $\sum_{i\in s}a_ib_i$ over `b` such that $\|b\|_q\le 1$. Now
Minkowski's inequality follows from the fact that the maximum value of the sum of two functions is
less than or equal to the sum of the maximum values of the summands.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `StrictConvexOn` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/

universe u v

open Finset NNReal ENNReal

open scoped BigOperators

noncomputable section

variable {ι : Type u} (s : Finset ι)

section GeomMeanLEArithMean

/-! ### AM-GM inequality -/

namespace Real

theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i := by
  -- If some number `z i` equals zero and has non-zero weight, then LHS is 0 and RHS is nonnegative.
  by_cases! A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · exact sum_nonneg fun j hj => mul_nonneg (hw j hj) (hz j hj)
    · rw [hzi]
      exact zero_rpow hwi
  -- If all numbers `z i` with non-zero weight are positive, then we apply Jensen's inequality
  -- for `exp` and numbers `log (z i)` with weights `w i`.
  · have := convexOn_exp.map_sum_le hw hw' fun i _ => Set.mem_univ <| log (z i)
    simp only [exp_sum, smul_eq_mul, mul_comm (w _) (log _)] at this
    convert this using 1 <;> [apply prod_congr rfl; apply sum_congr rfl] <;> intro i hi
    · rcases eq_or_lt_of_le (hz i hi) with hz | hz
      · simp [A i hi hz.symm]
      · exact rpow_def_of_pos hz _
    · rcases eq_or_lt_of_le (hz i hi) with hz | hz
      · simp [A i hi hz.symm]
      · rw [exp_log hz]

theorem geom_mean_le_arith_mean {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : 0 < ∑ i ∈ s, w i) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ ≤ (∑ i ∈ s, w i * z i) / (∑ i ∈ s, w i) := by
  convert geom_mean_le_arith_mean_weighted s (fun i => (w i) / ∑ i ∈ s, w i) z ?_ ?_ hz using 2
  · rw [← finset_prod_rpow _ _ (fun i hi => rpow_nonneg (hz _ hi) _) _]
    refine Finset.prod_congr rfl (fun _ ih => ?_)
    rw [div_eq_mul_inv, rpow_mul (hz _ ih)]
  · simp_rw [div_eq_mul_inv, mul_assoc, mul_comm, ← mul_assoc, ← Finset.sum_mul, mul_comm]
  · exact fun _ hi => div_nonneg (hw _ hi) (le_of_lt hw')
  · simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (by linarith)

-- DISSOLVED: geom_mean_weighted_of_constant

-- DISSOLVED: arith_mean_weighted_of_constant

-- DISSOLVED: geom_mean_eq_arith_mean_weighted_of_constant

theorem geom_mean_eq_arith_mean_weighted_iff' (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, z j = ∑ i ∈ s, w i * z i := by
  by_cases! A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · constructor
      · intro h
        rw [← h]
        intro j hj
        apply eq_zero_of_ne_zero_of_mul_left_eq_zero (ne_of_lt (hw j hj)).symm
        apply (sum_eq_zero_iff_of_nonneg ?_).mp h.symm j hj
        exact fun i hi => (mul_nonneg_iff_of_pos_left (hw i hi)).mpr (hz i hi)
      · intro h
        convert h i his
        exact hzi.symm
    · rw [hzi]
      exact zero_rpow hwi
  · have hz' := fun i h => lt_of_le_of_ne (hz i h) (fun a => (ne_of_gt (hw i h)) (A i h a.symm))
    have := strictConvexOn_exp.map_sum_eq_iff hw hw' fun i _ => Set.mem_univ <| log (z i)
    simp only [exp_sum, smul_eq_mul, mul_comm (w _) (log _)] at this
    convert this using 1
    · apply Eq.congr <;>
      [apply prod_congr rfl; apply sum_congr rfl] <;>
      intro i hi <;>
      simp only [exp_mul, exp_log (hz' i hi)]
    · constructor <;> intro h j hj
      · rw [← arith_mean_weighted_of_constant s w _ (log (z j)) hw' fun i _ => congrFun rfl]
        apply sum_congr rfl
        intro x hx
        simp only [mul_comm, h j hj, h x hx]
      · rw [← arith_mean_weighted_of_constant s w _ (z j) hw' fun i _ => congrFun rfl]
        apply sum_congr rfl
        intro x hx
        simp only [log_injOn_pos (hz' j hj) (hz' x hx), h j hj, h x hx]

-- DISSOLVED: geom_mean_eq_arith_mean_weighted_iff

theorem geom_mean_lt_arith_mean_weighted_iff_of_pos (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i < ∑ i ∈ s, w i * z i ↔ ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k := by
  constructor
  · intro h
    by_contra! h_contra
    rw [(geom_mean_eq_arith_mean_weighted_iff' s w z hw hw' hz).mpr ?_] at h
    · exact (lt_self_iff_false _).mp h
    · intro j hjs
      rw [← arith_mean_weighted_of_constant s w (fun _ => z j) (z j) hw' fun _ _ => congrFun rfl]
      apply sum_congr rfl (fun x a => congrArg (HMul.hMul (w x)) (h_contra j hjs x a))
  · rintro ⟨j, hjs, k, hks, hzjk⟩
    have := geom_mean_le_arith_mean_weighted s w z (fun i a => le_of_lt (hw i a)) hw' hz
    by_contra! h
    apply le_antisymm this at h
    apply (geom_mean_eq_arith_mean_weighted_iff' s w z hw hw' hz).mp at h
    simp only [h j hjs, h k hks, ne_eq, not_true_eq_false] at hzjk

end Real

namespace NNReal

theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) :
    (∏ i ∈ s, z i ^ (w i : ℝ)) ≤ ∑ i ∈ s, w i * z i :=
  mod_cast
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => (w i).coe_nonneg)
      (by assumption_mod_cast) fun i _ => (z i).coe_nonneg

theorem geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0) :
    w₁ + w₂ = 1 → p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one] using
    geom_mean_le_arith_mean_weighted univ ![w₁, w₂] ![p₁, p₂]

theorem geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0) :
    w₁ + w₂ + w₃ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃] ![p₁, p₂, p₃]

theorem geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ≥0) :
    w₁ + w₂ + w₃ + w₄ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) * p₄ ^ (w₄ : ℝ) ≤
        w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃, w₄] ![p₁, p₂, p₃, p₄]

end NNReal

namespace Real

theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) : p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
  NNReal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ <|
    NNReal.coe_inj.1 <| by assumption

theorem geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw₃ : 0 ≤ w₃) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hw : w₁ + w₂ + w₃ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
  NNReal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
      ⟨p₃, hp₃⟩ <|
    NNReal.coe_inj.1 hw

theorem geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ} (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hw₄ : 0 ≤ w₄) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hp₄ : 0 ≤ p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
  NNReal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩
      ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩ <|
    NNReal.coe_inj.1 <| by assumption

end Real

end GeomMeanLEArithMean

section HarmMeanLEGeomMean

/-! ### HM-GM inequality -/

namespace Real

theorem harm_mean_le_geom_mean_weighted (w z : ι → ℝ) (hs : s.Nonempty) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i / z i)⁻¹ ≤ ∏ i ∈ s, z i ^ w i := by
  have : ∏ i ∈ s, (1 / z) i ^ w i ≤ ∑ i ∈ s, w i * (1 / z) i :=
    geom_mean_le_arith_mean_weighted s w (1 / z) (fun i hi ↦ le_of_lt (hw i hi)) hw'
    (fun i hi ↦ one_div_nonneg.2 (le_of_lt (hz i hi)))
  have p_pos : 0 < ∏ i ∈ s, (z i)⁻¹ ^ w i :=
    prod_pos fun i hi => rpow_pos_of_pos (inv_pos.2 (hz i hi)) _
  have s_pos : 0 < ∑ i ∈ s, w i * (z i)⁻¹ :=
    sum_pos (fun i hi => mul_pos (hw i hi) (inv_pos.2 (hz i hi))) hs
  simp only [Pi.div_apply, Pi.one_apply, one_div, ← inv_le_inv₀ s_pos p_pos] at this
  apply le_trans this
  have p_pos₂ : 0 < (∏ i ∈ s, (z i) ^ w i)⁻¹ :=
    inv_pos.2 (prod_pos fun i hi => rpow_pos_of_pos ((hz i hi)) _)
  rw [← inv_inv (∏ i ∈ s, z i ^ w i), inv_le_inv₀ p_pos p_pos₂, ← Finset.prod_inv_distrib]
  gcongr
  · exact fun i hi ↦ by positivity [hz i hi]
  · rw [Real.inv_rpow]; apply fun i hi ↦ le_of_lt (hz i hi); assumption

theorem harm_mean_le_geom_mean {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) (hw' : 0 < ∑ i ∈ s, w i) (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i) / (∑ i ∈ s, w i / z i) ≤ (∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ := by
  have := harm_mean_le_geom_mean_weighted s (fun i => (w i) / ∑ i ∈ s, w i) z hs ?_ ?_ hz
  · simp only at this
    set n := ∑ i ∈ s, w i
    nth_rw 1 [div_eq_mul_inv, (show n = (n⁻¹)⁻¹ by simp), ← mul_inv, Finset.mul_sum _ _ n⁻¹]
    simp_rw [inv_mul_eq_div n ((w _) / (z _)), div_right_comm _ _ n]
    convert this
    rw [← Real.finset_prod_rpow s _ (fun i hi ↦ by positivity [hz i hi])]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [← Real.rpow_mul (le_of_lt <| hz i hi) (w _) n⁻¹, div_eq_mul_inv (w _) n]
  · exact fun i hi ↦ div_pos (hw i hi) hw'
  · simp_rw [div_eq_mul_inv (w _) (∑ i ∈ s, w i), ← Finset.sum_mul _ _ (∑ i ∈ s, w i)⁻¹]
    exact mul_inv_cancel₀ hw'.ne'

end Real

end HarmMeanLEGeomMean

section Young

/-! ### Young's inequality -/

namespace Real

theorem young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : p.HolderConjugate q) : a * b ≤ a ^ p / p + b ^ q / q := by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, _root_.div_eq_inv_mul] using
    geom_mean_le_arith_mean2_weighted hpq.inv_nonneg hpq.symm.inv_nonneg
      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one

theorem young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ |a| ^ p / p + |b| ^ q / q :=
  calc
    a * b ≤ |a * b| := le_abs_self (a * b)
    _ = |a| * |b| := abs_mul a b
    _ ≤ |a| ^ p / p + |b| ^ q / q :=
      Real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

end Real

namespace NNReal

theorem young_inequality (a b : ℝ≥0) {p q : ℝ≥0} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ (p : ℝ) / p + b ^ (q : ℝ) / q :=
  Real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

theorem young_inequality_real (a b : ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / Real.toNNReal p + b ^ q / Real.toNNReal q := by
  simpa [Real.coe_toNNReal, hpq.nonneg, hpq.symm.nonneg] using young_inequality a b hpq.toNNReal

end NNReal

namespace ENNReal

theorem young_inequality (a b : ℝ≥0∞) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / ENNReal.ofReal p + b ^ q / ENNReal.ofReal q := by
  by_cases! h : a = ⊤ ∨ b = ⊤
  · refine le_trans le_top (le_of_eq ?_)
    repeat rw [div_eq_mul_inv]
    rcases h with h | h <;> rw [h] <;> simp [hpq.pos, hpq.symm.pos]
  -- if a ≠ ⊤ and b ≠ ⊤, use the nnreal version: nnreal.young_inequality_real
  rw [← coe_toNNReal h.left, ← coe_toNNReal h.right, ← coe_mul, ← coe_rpow_of_nonneg _ hpq.nonneg,
    ← coe_rpow_of_nonneg _ hpq.symm.nonneg, ENNReal.ofReal, ENNReal.ofReal, ←
    @coe_div (Real.toNNReal p) _ (by simp [hpq.pos]), ←
    @coe_div (Real.toNNReal q) _ (by simp [hpq.symm.pos]), ← coe_add, coe_le_coe]
  exact NNReal.young_inequality_real a.toNNReal b.toNNReal hpq

end ENNReal

end Young

section HoelderMinkowski

/-! ### Hölder's and Minkowski's inequalities -/

namespace NNReal

private theorem inner_le_Lp_mul_Lp_of_norm_le_one (f g : ι → ℝ≥0) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : ∑ i ∈ s, f i ^ p ≤ 1) (hg : ∑ i ∈ s, g i ^ q ≤ 1) :
    ∑ i ∈ s, f i * g i ≤ 1 := by
  have hp : 0 < p.toNNReal := zero_lt_one.trans hpq.toNNReal.lt
  have hq : 0 < q.toNNReal := zero_lt_one.trans hpq.toNNReal.symm.lt
  calc
    ∑ i ∈ s, f i * g i ≤ ∑ i ∈ s, (f i ^ p / Real.toNNReal p + g i ^ q / Real.toNNReal q) :=
      Finset.sum_le_sum fun i _ => young_inequality_real (f i) (g i) hpq
    _ = (∑ i ∈ s, f i ^ p) / Real.toNNReal p + (∑ i ∈ s, g i ^ q) / Real.toNNReal q := by
      rw [sum_add_distrib, sum_div, sum_div]
    _ ≤ 1 / Real.toNNReal p + 1 / Real.toNNReal q := by gcongr
    _ = 1 := by simp_rw [one_div, hpq.toNNReal.inv_add_inv_eq_one]

private theorem inner_le_Lp_mul_Lp_of_norm_eq_zero (f g : ι → ℝ≥0) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : ∑ i ∈ s, f i ^ p = 0) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  simp only [hf, hpq.ne_zero, one_div, sum_eq_zero_iff, zero_rpow, zero_mul,
    inv_eq_zero, Ne, not_false_iff, le_zero_iff, mul_eq_zero]
  intro i his
  left
  rw [sum_eq_zero_iff] at hf
  exact (rpow_eq_zero_iff.mp (hf i his)).left

theorem inner_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  obtain hf | hf := eq_zero_or_pos (∑ i ∈ s, f i ^ p)
  · exact inner_le_Lp_mul_Lp_of_norm_eq_zero s f g hpq hf
  obtain hg | hg := eq_zero_or_pos (∑ i ∈ s, g i ^ q)
  · calc
      ∑ i ∈ s, f i * g i = ∑ i ∈ s, g i * f i := by
        congr with i
        rw [mul_comm]
      _ ≤ (∑ i ∈ s, g i ^ q) ^ (1 / q) * (∑ i ∈ s, f i ^ p) ^ (1 / p) :=
        (inner_le_Lp_mul_Lp_of_norm_eq_zero s g f hpq.symm hg)
      _ = (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := mul_comm _ _
  let f' i := f i / (∑ i ∈ s, f i ^ p) ^ (1 / p)
  let g' i := g i / (∑ i ∈ s, g i ^ q) ^ (1 / q)
  suffices (∑ i ∈ s, f' i * g' i) ≤ 1 by
    simp_rw [f', g', div_mul_div_comm, ← sum_div] at this
    rwa [div_le_iff₀, one_mul] at this
    positivity
  refine inner_le_Lp_mul_Lp_of_norm_le_one s f' g' hpq (le_of_eq ?_) (le_of_eq ?_)
  · simp_rw [f', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel₀ hpq.ne_zero, rpow_one,
      div_self hf.ne']
  · simp_rw [g', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel₀ hpq.symm.ne_zero,
      rpow_one, div_self hg.ne']

theorem Lr_rpow_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q r : ℝ} (hpqr : p.HolderTriple q r) :
    ∑ i ∈ s, (f i * g i) ^ r ≤ (∑ i ∈ s, f i ^ p) ^ (r / p) * (∑ i ∈ s, g i ^ q) ^ (r / q) := by
  simpa [mul_rpow, ← NNReal.rpow_mul, ← mul_div_assoc, hpqr.pos'.ne', fieldEq] using
    inner_le_Lp_mul_Lq s (fun i ↦ f i ^ r) (fun i ↦ g i ^ r) hpqr.holderConjugate_div_div

theorem Lr_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q r : ℝ} (hpqr : p.HolderTriple q r) :
    (∑ i ∈ s, (f i * g i) ^ r) ^ (1 / r) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  convert rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos' : 0 < 1 / r) |>.mpr <|
    Lr_rpow_le_Lp_mul_Lq s f g hpqr using 1
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

lemma inner_le_weight_mul_Lp (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ≥0) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  calc
    _ = ∑ i ∈ s, w i ^ (1 - p⁻¹) * (w i ^ p⁻¹ * f i) := ?_
    _ ≤ (∑ i ∈ s, (w i ^ (1 - p⁻¹)) ^ (1 - p⁻¹)⁻¹) ^ (1 / (1 - p⁻¹)⁻¹) *
          (∑ i ∈ s, (w i ^ p⁻¹ * f i) ^ p) ^ (1 / p) :=
        inner_le_Lp_mul_Lq _ _ _ (.symm <| Real.holderConjugate_iff.mpr ⟨hp, by simp⟩)
    _ = _ := ?_
  · congr with i
    rw [← mul_assoc, ← rpow_of_add_eq _ one_ne_zero, rpow_one]
    simp
  · have hp₀ : p ≠ 0 := by positivity
    have hp₁ : 1 - p⁻¹ ≠ 0 := by simp [sub_eq_zero, hp.ne']
    simp [mul_rpow, div_inv_eq_mul, one_mul, one_div, hp₀, hp₁]

theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ}
    (hpqr : p.HolderTriple q r) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => (f i * g i) ^ r) ∧
      ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
  have H₁ : ∀ s : Finset ι,
      ∑ i ∈ s, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
    intro s
    obtain ⟨hp, hq, hr⟩ := hpqr.all_pos
    refine le_trans (Lr_rpow_le_Lp_mul_Lq s f g hpqr) (mul_le_mul ?_ ?_ bot_le bot_le)
    · gcongr
      exact hf.sum_le_tsum _ (fun _ _ => zero_le _)
    · gcongr
      exact hg.sum_le_tsum _ (fun _ _ => zero_le _)
  have bdd : BddAbove (Set.range fun s => ∑ i ∈ s, (f i * g i) ^ r) := by
    refine ⟨(∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q), ?_⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (hasSum_of_isLUB _ (isLUB_ciSup bdd)).summable
  exact ⟨H₂, H₂.tsum_le_of_sum_le H₁⟩

theorem summable_and_inner_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpq hf hg

theorem summable_mul_rpow_of_Lp_Lq {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => (f i * g i) ^ r :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).1

theorem summable_mul_of_Lp_Lq {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).1

theorem Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).2

theorem Lr_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (∑' i, (f i * g i) ^ r) ^ (1 / r) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  convert rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos') |>.mpr <|
    Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

theorem inner_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).2
