/-
Extracted from NumberTheory/LSeries/RiemannZeta.lean
Genuine: 25 of 30 | Dissolved: 2 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.PSeriesComplex

/-!
# Definition of the Riemann zeta function

## Main definitions:

* `riemannZeta`: the Riemann zeta function `ζ : ℂ → ℂ`.
* `completedRiemannZeta`: the completed zeta function `Λ : ℂ → ℂ`, which satisfies
  `Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (away from the poles of `Γ(s / 2)`).
* `completedRiemannZeta₀`: the entire function `Λ₀` satisfying
  `Λ₀(s) = Λ(s) + 1 / (s - 1) - 1 / s` wherever the RHS is defined.

Note that mathematically `ζ(s)` is undefined at `s = 1`, while `Λ(s)` is undefined at both `s = 0`
and `s = 1`. Our construction assigns some values at these points; exact formulae involving the
Euler-Mascheroni constant will follow in a subsequent PR.

## Main results:

* `differentiable_completedZeta₀` : the function `Λ₀(s)` is entire.
* `differentiableAt_completedZeta` : the function `Λ(s)` is differentiable away from `s = 0` and
  `s = 1`.
* `differentiableAt_riemannZeta` : the function `ζ(s)` is differentiable away from `s = 1`.
* `zeta_eq_tsum_one_div_nat_add_one_cpow` : for `1 < re s`, we have
  `ζ(s) = ∑' (n : ℕ), 1 / (n + 1) ^ s`.
* `completedRiemannZeta₀_one_sub`, `completedRiemannZeta_one_sub`, and `riemannZeta_one_sub` :
  functional equation relating values at `s` and `1 - s`

For special-value formulae expressing `ζ (2 * k)` and `ζ (1 - 2 * k)` in terms of Bernoulli numbers
see `Mathlib.NumberTheory.LSeries.HurwitzZetaValues`. For computation of the constant term as
`s → 1`, see `Mathlib.NumberTheory.Harmonic.ZetaAsymp`.

## Outline of proofs:

These results are mostly special cases of more general results for even Hurwitz zeta functions
proved in `Mathlib.NumberTheory.LSeries.HurwitzZetaEven`.
-/

open CharZero MeasureTheory Set Filter Asymptotics TopologicalSpace Real Asymptotics

  Classical HurwitzZeta

open Complex hiding exp norm_eq_abs abs_of_nonneg abs_two continuous_exp

open scoped Topology Real Nat

noncomputable section

/-!
## Definition of the completed Riemann zeta
-/

def completedRiemannZeta₀ (s : ℂ) : ℂ := completedHurwitzZetaEven₀ 0 s

def completedRiemannZeta (s : ℂ) : ℂ := completedHurwitzZetaEven 0 s

lemma HurwitzZeta.completedHurwitzZetaEven_zero (s : ℂ) :
    completedHurwitzZetaEven 0 s = completedRiemannZeta s := rfl

lemma HurwitzZeta.completedHurwitzZetaEven₀_zero (s : ℂ) :
    completedHurwitzZetaEven₀ 0 s = completedRiemannZeta₀ s := rfl

lemma HurwitzZeta.completedCosZeta_zero (s : ℂ) :
    completedCosZeta 0 s = completedRiemannZeta s := by
  rw [completedRiemannZeta, completedHurwitzZetaEven, completedCosZeta, hurwitzEvenFEPair_zero_symm]

lemma HurwitzZeta.completedCosZeta₀_zero (s : ℂ) :
    completedCosZeta₀ 0 s = completedRiemannZeta₀ s := by
  rw [completedRiemannZeta₀, completedHurwitzZetaEven₀, completedCosZeta₀,
    hurwitzEvenFEPair_zero_symm]

lemma completedRiemannZeta_eq (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  simp_rw [completedRiemannZeta, completedRiemannZeta₀, completedHurwitzZetaEven_eq, if_true]

theorem differentiable_completedZeta₀ : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedHurwitzZetaEven₀ 0

-- DISSOLVED: differentiableAt_completedZeta

theorem completedRiemannZeta₀_one_sub (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s := by
  rw [← completedHurwitzZetaEven₀_zero, ← completedCosZeta₀_zero, completedHurwitzZetaEven₀_one_sub]

theorem completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  rw [← completedHurwitzZetaEven_zero, ← completedCosZeta_zero, completedHurwitzZetaEven_one_sub]

lemma completedRiemannZeta_residue_one :
    Tendsto (fun s ↦ (s - 1) * completedRiemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  completedHurwitzZetaEven_residue_one 0

/-!
## The un-completed Riemann zeta function
-/

def riemannZeta := hurwitzZetaEven 0

lemma HurwitzZeta.hurwitzZetaEven_zero : hurwitzZetaEven 0 = riemannZeta := rfl

lemma HurwitzZeta.cosZeta_zero : cosZeta 0 = riemannZeta := by
  simp_rw [cosZeta, riemannZeta, hurwitzZetaEven, if_true, completedHurwitzZetaEven_zero,
    completedCosZeta_zero]

lemma HurwitzZeta.hurwitzZeta_zero : hurwitzZeta 0 = riemannZeta := by
  ext1 s
  simpa [hurwitzZeta, hurwitzZetaEven_zero] using hurwitzZetaOdd_neg 0 s

lemma HurwitzZeta.expZeta_zero : expZeta 0 = riemannZeta := by
  ext1 s
  rw [expZeta, cosZeta_zero, add_right_eq_self, mul_eq_zero, eq_false_intro I_ne_zero, false_or,
    ← eq_neg_self_iff, ← sinZeta_neg, neg_zero]

theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_hurwitzZetaEven _ hs'

theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
  simp_rw [riemannZeta, hurwitzZetaEven, Function.update_same, if_true]

-- DISSOLVED: riemannZeta_def_of_ne_zero

theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
  hurwitzZetaEven_neg_two_mul_nat_add_one 0 n

theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s := by
  rw [riemannZeta, hurwitzZetaEven_one_sub 0 hs (Or.inr hs'), cosZeta_zero, hurwitzZetaEven_zero]

def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2

/-!
## Relating the Mellin transform to the Dirichlet series
-/

theorem completedZeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    completedRiemannZeta s =
      (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  have := (hasSum_nat_completedCosZeta 0 hs).tsum_eq.symm
  simp only [QuotientAddGroup.mk_zero, completedCosZeta_zero] at this
  simp only [this, Gammaℝ_def, mul_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one, mul_one_div,
    ← tsum_mul_left]
  congr 1 with n
  split_ifs with h
  · simp only [h, Nat.cast_zero, zero_cpow (Complex.ne_zero_of_one_lt_re hs), div_zero]
  · rfl

theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  simpa only [QuotientAddGroup.mk_zero, cosZeta_zero, mul_zero, zero_mul, Real.cos_zero,
    ofReal_one] using (hasSum_nat_cosZeta 0 hs).tsum_eq.symm

theorem zeta_eq_tsum_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s := by
  have := zeta_eq_tsum_one_div_nat_cpow hs
  rw [tsum_eq_zero_add] at this
  · simpa [zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · rwa [Complex.summable_one_div_nat_cpow]

theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) :
    riemannZeta k = ∑' n : ℕ, 1 / (n : ℂ) ^ k := by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_natCast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_natCast]

lemma riemannZeta_residue_one : Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by
  exact hurwitzZetaEven_residue_one 0

theorem tendsto_sub_mul_tsum_nat_cpow :
    Tendsto (fun s : ℂ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℂ) ^ s) (𝓝[{s | 1 < re s}] 1) (𝓝 1) := by
  refine (tendsto_nhdsWithin_mono_left ?_ riemannZeta_residue_one).congr' ?_
  · simp only [subset_compl_singleton_iff, mem_setOf_eq, one_re, not_lt, le_refl]
  · filter_upwards [eventually_mem_nhdsWithin] with s hs using
      congr_arg _ <| zeta_eq_tsum_one_div_nat_cpow hs

theorem tendsto_sub_mul_tsum_nat_rpow :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℝ) ^ s) (𝓝[>] 1) (𝓝 1) := by
  rw [← tendsto_ofReal_iff, ofReal_one]
  have : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[{s | 1 < re s}] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ ↦ by aesop)
  apply (tendsto_sub_mul_tsum_nat_cpow.comp this).congr fun s ↦ ?_
  simp only [one_div, Function.comp_apply, ofReal_mul, ofReal_sub, ofReal_one, ofReal_tsum,
    ofReal_inv, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]

section aliases

noncomputable alias riemannCompletedZeta₀ := completedRiemannZeta₀

noncomputable alias riemannCompletedZeta := completedRiemannZeta

alias riemannCompletedZeta₀_one_sub := completedRiemannZeta₀_one_sub

alias riemannCompletedZeta_one_sub := completedRiemannZeta_one_sub

alias riemannCompletedZeta_residue_one := completedRiemannZeta_residue_one

end aliases
