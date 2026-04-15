/-
Extracted from NumberTheory/LSeries/Nonvanishing.lean
Genuine: 17 of 27 | Dissolved: 10 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Positivity

/-!
# The L-function of a Dirichlet character does not vanish on Re(s) ≥ 1

The main result in this file is `DirichletCharacter.Lfunction_ne_zero_of_one_le_re`:
if `χ` is a Dirichlet character, `s ∈ ℂ` with `1 ≤ s.re`, and either `χ` is nontrivial or `s ≠ 1`,
then the L-function of `χ` does not vanish at `s`.

As a consequence, we have the corresponding statement for the Riemann ζ function:
`riemannZeta_ne_zero_of_one_le_re` (which does not require `s ≠ 1`, since the junk value at `s = 1`
happens to be non-zero).

These results are prerequisites for the **Prime Number Theorem** and
**Dirichlet's Theorem** on primes in arithmetic progressions.

## Outline of proofs

We split into two cases: first, the special case of (non-trivial) quadratic characters at `s = 1`;
then the remaining case when either `s ≠ 1` or `χ ^ 2 ≠ 1`.

The first case is handled using a positivity argument applied to the series `L χ s * ζ s`: we show
that this function has non-negative Dirichlet coefficients, is strictly positive for `s ≫ 0`, but
vanishes at `s = -2`, so it must have a pole somewhere in between.

The second case is dealt with using the product
`L(χ^0, 1 + x)^3 L(χ, 1 + x + I * y)^4 L(χ^2, 1 + x + 2 * I * y)`, which
we show has absolute value `≥ 1` for all positive `x` and real `y`; if `L(χ, 1 + I * y) = 0` then
this product would have to tend to 0 as `x → 0`, which is a contradiction.
-/

open Complex Asymptotics Topology Filter

open ArithmeticFunction hiding log

open scoped ComplexOrder

variable {N : ℕ}

namespace DirichletCharacter

section quadratic

/-!
### Convolution of a Dirichlet character with ζ

We define `DirichletCharacter.zetaMul χ` to be the arithmetic function obtained by
taking the product (as arithmetic functions = Dirichlet convolution) of the
arithmetic function `ζ` with `χ`.

We then show that for a quadratic character `χ`, this arithmetic function is multiplicative
and takes nonnegative real values.
-/

def zetaMul (χ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  .zeta * toArithmeticFunction (χ ·)

lemma isMultiplicative_zetaMul (χ : DirichletCharacter ℂ N) : χ.zetaMul.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul <| isMultiplicative_toArithmeticFunction χ

lemma LSeriesSummable_zetaMul (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable χ.zetaMul s := by
  refine ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zeta_iff.mpr hs) <|
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn ↦ ?_) hs
  simpa only [toArithmeticFunction, coe_mk, hn, ↓reduceIte, ← Complex.norm_eq_abs]
  using norm_le_one χ _

lemma zetaMul_prime_pow_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    0 ≤ zetaMul χ (p ^ k) := by
  simp only [zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, le_refl, pow_nonneg]
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]
    split_ifs
    exacts [le_rfl, zero_le_one]

lemma zetaMul_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ zetaMul χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [χ.isMultiplicative_zetaMul.multiplicative_factorization _ hn] using
      Finset.prod_nonneg
        fun p hp ↦ zetaMul_prime_pow_nonneg hχ (Nat.prime_of_mem_primeFactors hp) _

-- DISSOLVED: BadChar

variable [NeZero N]

namespace BadChar

private noncomputable

def F (B : BadChar N) : ℂ → ℂ :=
  Function.update (fun s : ℂ ↦ riemannZeta s * LFunction B.χ s) 1 (deriv (LFunction B.χ) 1)

private lemma F_differentiableAt_of_ne (B : BadChar N) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ B.F s := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · exact (differentiableAt_riemannZeta hs).mul <| differentiableAt_LFunction B.χ s (.inl hs)
  · filter_upwards [eventually_ne_nhds hs] with t ht using Function.update_noteq ht ..

private lemma F_eq_LSeries (B : BadChar N) {s : ℂ} (hs : 1 < s.re) :
    B.F s = LSeries B.χ.zetaMul s := by
  rw [F, zetaMul, ← coe_mul, LSeries_convolution']
  · have hs' : s ≠ 1 := fun h ↦ by simp only [h, one_re, lt_self_iff_false] at hs
    simp only [ne_eq, hs', not_false_eq_true, Function.update_noteq, B.χ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr s B.χ.apply_eq_toArithmeticFunction_apply
  -- summability side goals from `LSeries_convolution'`
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (B.χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re B.χ hs

private lemma F_differentiable (B : BadChar N) : Differentiable ℂ B.F := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact B.F_differentiableAt_of_ne hs
  -- now need to deal with `s = 1`
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact B.F_differentiableAt_of_ne ht
  -- now reduced to showing *continuity* at s = 1
  let G := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
  let H := Function.update (fun s ↦ (B.χ.LFunction s - B.χ.LFunction 1) / (s - 1)) 1
    (deriv B.χ.LFunction 1)
  have : B.F = G * H := by
    ext1 t
    rcases eq_or_ne t 1 with rfl | ht
    · simp only [F, G, H, Pi.mul_apply, one_mul, Function.update_same]
    · simp only [F, G, H, Function.update_noteq ht, mul_comm _ (riemannZeta _), B.hχ, sub_zero,
      Pi.mul_apply, mul_assoc, mul_div_cancel₀ _ (sub_ne_zero.mpr ht)]
  rw [this]
  apply ContinuousAt.mul
  · simpa only [G, continuousAt_update_same] using riemannZeta_residue_one
  · exact (B.χ.differentiableAt_LFunction 1 (.inr B.χ_ne)).hasDerivAt.continuousAt_div

private lemma F_neg_two (B : BadChar N) : B.F (-2 : ℝ) = 0 := by
  have := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero, zero_add, mul_one] at this
  rw [F, ofReal_neg, ofReal_ofNat, Function.update_noteq (mod_cast (by omega : (-2 : ℤ) ≠ 1)),
    this, zero_mul]

end BadChar

-- DISSOLVED: LFunction_apply_one_ne_zero_of_quadratic

end quadratic

section nonvanishing

variable (χ : DirichletCharacter ℂ N)

private lemma re_log_comb_nonneg' {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
      0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [norm_eq_abs, abs_ofReal, _root_.abs_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [pow_zero, Nat.cast_zero, div_zero, mul_zero, one_re, mul_one, add_zero, le_refl]
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_abs_sub_sq_re, ← norm_eq_abs, norm_pow,
      hz]
    convert (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

private lemma re_log_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    0 ≤ 3 * (-log (1 - (1 : DirichletCharacter ℂ N) n * n ^ (-x : ℂ))).re +
          4 * (-log (1 - χ n * n ^ (-(x + I * y)))).re +
          (-log (1 - (χ n ^ 2) * n ^ (-(x + 2 * I * y)))).re := by
  by_cases hn' : IsUnit (n : ZMod N)
  · have ha₀ : 0 ≤ (n : ℝ) ^ (-x) := Real.rpow_nonneg n.cast_nonneg _
    have ha₁ : (n : ℝ) ^ (-x) < 1 := by
      rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
      exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
    have hz : ‖χ n * (n : ℂ) ^ (-(I * y))‖ = 1 := by
      rw [norm_mul, ← hn'.unit_spec, DirichletCharacter.unit_norm_eq_one χ hn'.unit,
        norm_eq_abs, ← ofReal_natCast, abs_cpow_eq_rpow_re_of_pos (mod_cast by omega)]
      simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
        neg_zero, Real.rpow_zero, one_mul]
    rw [MulChar.one_apply hn', one_mul]
    convert re_log_comb_nonneg' ha₀ ha₁ hz using 6
    · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
    · congr 2
      rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, mul_left_comm]
    · rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow,
        mul_left_comm]
  · simp only [MulChar.map_nonunit _ hn', zero_mul, sub_zero, log_one, neg_zero, zero_re, mul_zero,
      neg_add_rev, add_zero, pow_two, le_refl]

lemma summable_neg_log_one_sub_mul_prime_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes ↦ -log (1 - χ p * (p : ℂ) ^ (-s)) := by
  have (p : Nat.Primes) : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s).re := by
    simpa only [norm_mul, norm_natCast_cpow_of_re_ne_zero _ <| re_neg_ne_zero_of_one_lt_re hs]
      using mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  refine (Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le (fun _ ↦ norm_nonneg _) this
    |>.of_norm.clog_one_sub.neg
  simp only [neg_re, neg_lt_neg_iff, hs]

private lemma one_lt_re_one_add {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 < (1 + x : ℂ).re ∧ 1 < (1 + x + I * y).re ∧ 1 < (1 + x + 2 * I * y).re := by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im, and_self]

open scoped LSeries.notation in

lemma norm_LSeries_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖L ↗(1 : DirichletCharacter ℂ N) (1 + x) ^ 3 * L ↗χ (1 + x + I * y) ^ 4 *
      L ↗(χ ^ 2 :) (1 + x + 2 * I * y)‖ ≥ 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  have H₀ := summable_neg_log_one_sub_mul_prime_cpow (N := N) 1 h₀
  have H₁ := summable_neg_log_one_sub_mul_prime_cpow χ h₁
  have H₂ := summable_neg_log_one_sub_mul_prime_cpow (χ ^ 2) h₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← LSeries_eulerProduct_exp_log _ h₀, ← LSeries_eulerProduct_exp_log χ h₁,
    ← LSeries_eulerProduct_exp_log _ h₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_eq_abs, abs_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_add hsum₀ hsum₁, ← tsum_add (hsum₀.add hsum₁) hsum₂]
  simpa only [neg_add_rev, neg_re, mul_neg, χ.pow_apply' two_ne_zero, ge_iff_le, add_re, one_re,
    ofReal_re, ofReal_add, ofReal_one] using
      tsum_nonneg fun (p : Nat.Primes) ↦ χ.re_log_comb_nonneg p.prop.two_le h₀ y

variable [NeZero N]

lemma norm_LFunction_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * y) ^ 4 *
      LFunction (χ ^ 2) (1 + x + 2 * I * y)‖ ≥ 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  rw [LFunctionTrivChar, DirichletCharacter.LFunction_eq_LSeries 1 h₀,
    χ.LFunction_eq_LSeries h₁, (χ ^ 2).LFunction_eq_LSeries h₂]
  exact norm_LSeries_product_ge_one χ hx y

lemma LFunctionTrivChar_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ LFunctionTrivChar N (1 + x)) =O[𝓝[>] 0] fun x ↦ (1 : ℂ) / x := by
  have : (fun w : ℂ ↦ LFunctionTrivChar N (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * LFunctionTrivChar N (1 + w)) (𝓝[≠] 0)
        (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
      convert (LFunctionTrivChar_residue_one (N := N)).comp (f := fun w ↦ 1 + w) ?_ using 1
      · simp only [Function.comp_def, add_sub_cancel_left]
      · simpa only [tendsto_iff_comap, Homeomorph.coe_addLeft, add_zero, map_le_iff_le_comap] using
          ((Homeomorph.addLeft (1 : ℂ)).map_punctured_nhds_eq 0).le
    exact (isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <| H.isBigO_one ℂ
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhds_right'_le_nhds_ne 0

omit [NeZero N] in

-- DISSOLVED: one_add_I_mul_ne_one_or

-- DISSOLVED: LFunction_isBigO_horizontal

-- DISSOLVED: LFunction_isBigO_horizontal_of_eq_zero

-- DISSOLVED: LFunction_ne_zero_of_not_quadratic_or_ne_one

-- DISSOLVED: LFunction_ne_zero_of_re_eq_one

-- DISSOLVED: LFunction_ne_zero_of_one_le_re

variable {χ} in

-- DISSOLVED: LFunction_apply_one_ne_zero

-- DISSOLVED: _root_.riemannZeta_ne_zero_of_one_le_re

end nonvanishing

end DirichletCharacter
