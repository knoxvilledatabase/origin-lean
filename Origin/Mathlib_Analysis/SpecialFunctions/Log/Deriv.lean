/-
Extracted from Analysis/SpecialFunctions/Log/Deriv.lean
Genuine: 9 of 34 | Dissolved: 24 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.AdaptationNote

/-!
# Derivative and series expansion of real logarithm

In this file we prove that `Real.log` is infinitely smooth at all nonzero `x : ℝ`. We also prove
that the series `∑' n : ℕ, x ^ (n + 1) / (n + 1)` converges to `(-Real.log (1 - x))` for all
`x : ℝ`, `|x| < 1`.

## Tags

logarithm, derivative
-/

open Filter Finset Set

open scoped Topology ContDiff

namespace Real

variable {x : ℝ}

theorem hasStrictDerivAt_log_of_pos (hx : 0 < x) : HasStrictDerivAt log x⁻¹ x := by
  have : HasStrictDerivAt log (exp <| log x)⁻¹ x :=
    (hasStrictDerivAt_exp <| log x).of_local_left_inverse (continuousAt_log hx.ne')
        (ne_of_gt <| exp_pos _) <|
      Eventually.mono (lt_mem_nhds hx) @exp_log
  rwa [exp_log hx] at this

-- DISSOLVED: hasStrictDerivAt_log

-- DISSOLVED: hasDerivAt_log

-- DISSOLVED: differentiableAt_log

theorem differentiableOn_log : DifferentiableOn ℝ log {0}ᶜ := fun _x hx =>
  (differentiableAt_log hx).differentiableWithinAt

-- DISSOLVED: differentiableAt_log_iff

theorem deriv_log (x : ℝ) : deriv log x = x⁻¹ :=
  if hx : x = 0 then by
    rw [deriv_zero_of_not_differentiableAt (differentiableAt_log_iff.not_left.2 hx), hx, inv_zero]
  else (hasDerivAt_log hx).deriv

@[simp]
theorem deriv_log' : deriv log = Inv.inv :=
  funext deriv_log

-- DISSOLVED: contDiffAt_log

theorem contDiffOn_log {n : WithTop ℕ∞} : ContDiffOn ℝ n log {0}ᶜ := by
  intro x hx
  simp only [mem_compl_iff, mem_singleton_iff] at hx
  exact (contDiffAt_log.2 hx).contDiffWithinAt

end Real

section LogDifferentiable

open Real

section deriv

variable {f : ℝ → ℝ} {x f' : ℝ} {s : Set ℝ}

-- DISSOLVED: HasDerivWithinAt.log

-- DISSOLVED: HasDerivAt.log

-- DISSOLVED: HasStrictDerivAt.log

-- DISSOLVED: derivWithin.log

-- DISSOLVED: deriv.log

-- DISSOLVED: Real.deriv_log_comp_eq_logDeriv

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ}
  {s : Set E}

-- DISSOLVED: HasFDerivWithinAt.log

-- DISSOLVED: HasFDerivAt.log

-- DISSOLVED: HasStrictFDerivAt.log

-- DISSOLVED: DifferentiableWithinAt.log

-- DISSOLVED: DifferentiableAt.log

-- DISSOLVED: ContDiffAt.log

-- DISSOLVED: ContDiffWithinAt.log

-- DISSOLVED: ContDiffOn.log

-- DISSOLVED: ContDiff.log

-- DISSOLVED: DifferentiableOn.log

-- DISSOLVED: Differentiable.log

-- DISSOLVED: fderivWithin.log

-- DISSOLVED: fderiv.log

end fderiv

end LogDifferentiable

namespace Real

theorem tendsto_mul_log_one_plus_div_atTop (t : ℝ) :
    Tendsto (fun x => x * log (1 + t / x)) atTop (𝓝 t) := by
  have h₁ : Tendsto (fun h => h⁻¹ * log (1 + t * h)) (𝓝[≠] 0) (𝓝 t) := by
    simpa [hasDerivAt_iff_tendsto_slope, slope_fun_def] using
      (((hasDerivAt_id (0 : ℝ)).const_mul t).const_add 1).log (by simp)
  have h₂ : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_inv_atTop_zero'.mono_right (nhdsWithin_mono _ fun x hx => (Set.mem_Ioi.mp hx).ne')
  simpa only [Function.comp_def, inv_inv] using h₁.comp h₂

theorem abs_log_sub_add_sum_range_le {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + log (1 - x)| ≤ |x| ^ (n + 1) / (1 - |x|) := by
  /- For the proof, we show that the derivative of the function to be estimated is small,
    and then apply the mean value inequality. -/
  let F : ℝ → ℝ := fun x => (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + log (1 - x)
  let F' : ℝ → ℝ := fun x ↦ -x ^ n / (1 - x)
  -- Porting note: In `mathlib3`, the proof used `deriv`/`DifferentiableAt`. `simp` failed to
  -- compute `deriv`, so I changed the proof to use `HasDerivAt` instead
  -- First step: compute the derivative of `F`
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (F' y) y := fun y hy ↦ by
    have : HasDerivAt F ((∑ i ∈ range n, ↑(i + 1) * y ^ i / (↑i + 1)) + (-1) / (1 - y)) y :=
      .add (.sum fun i _ ↦ (hasDerivAt_pow (i + 1) y).div_const ((i : ℝ) + 1))
        (((hasDerivAt_id y).const_sub _).log <| sub_ne_zero.2 hy.2.ne')
    convert this using 1
    calc
      -y ^ n / (1 - y) = ∑ i ∈ Finset.range n, y ^ i + -1 / (1 - y) := by
        field_simp [geom_sum_eq hy.2.ne, sub_ne_zero.2 hy.2.ne, sub_ne_zero.2 hy.2.ne']
        ring
      _ = ∑ i ∈ Finset.range n, ↑(i + 1) * y ^ i / (↑i + 1) + -1 / (1 - y) := by
        congr with i
        rw [Nat.cast_succ, mul_div_cancel_left₀ _ (Nat.cast_add_one_pos i).ne']
  -- second step: show that the derivative of `F` is small
  have B : ∀ y ∈ Icc (-|x|) |x|, |F' y| ≤ |x| ^ n / (1 - |x|) := fun y hy ↦
    calc
      |F' y| = |y| ^ n / |1 - y| := by simp [F', abs_div]
      _ ≤ |x| ^ n / (1 - |x|) := by
        have : |y| ≤ |x| := abs_le.2 hy
        have : 1 - |x| ≤ |1 - y| := le_trans (by linarith [hy.2]) (le_abs_self _)
        gcongr
        exact sub_pos.2 h
  -- third step: apply the mean value inequality
  have C : ‖F x - F 0‖ ≤ |x| ^ n / (1 - |x|) * ‖x - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy ↦ (A _ ?_).hasDerivWithinAt) B (convex_Icc _ _) ?_ ?_
    · exact Icc_subset_Ioo (neg_lt_neg h) h hy
    · simp
    · simp [le_abs_self x, neg_le.mp (neg_le_abs x)]
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, div_mul_eq_mul_div, pow_succ] using C

theorem hasSum_pow_div_log_of_abs_lt_one {x : ℝ} (h : |x| < 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / (n + 1)) (-log (1 - x)) := by
  rw [Summable.hasSum_iff_tendsto_nat]
  · show Tendsto (fun n : ℕ => ∑ i ∈ range n, x ^ (i + 1) / (i + 1)) atTop (𝓝 (-log (1 - x)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [norm_eq_abs, sub_neg_eq_add]
    refine squeeze_zero (fun n => abs_nonneg _) (abs_log_sub_add_sum_range_le h) ?_
    suffices Tendsto (fun t : ℕ => |x| ^ (t + 1) / (1 - |x|)) atTop (𝓝 (|x| * 0 / (1 - |x|))) by
      simpa
    simp only [pow_succ']
    refine (tendsto_const_nhds.mul ?_).div_const _
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) h
  show Summable fun n : ℕ => x ^ (n + 1) / (n + 1)
  refine .of_norm_bounded _ (summable_geometric_of_lt_one (abs_nonneg _) h) fun i => ?_
  calc
    ‖x ^ (i + 1) / (i + 1)‖ = |x| ^ (i + 1) / (i + 1) := by
      have : (0 : ℝ) ≤ i + 1 := le_of_lt (Nat.cast_add_one_pos i)
      rw [norm_eq_abs, abs_div, ← pow_abs, abs_of_nonneg this]
    _ ≤ |x| ^ (i + 1) / (0 + 1) := by
      gcongr
      exact i.cast_nonneg
    _ ≤ |x| ^ i := by
      simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) i) (le_of_lt h)

theorem hasSum_log_sub_log_of_abs_lt_one {x : ℝ} (h : |x| < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * x ^ (2 * k + 1))
      (log (1 + x) - log (1 - x)) := by
  set term := fun n : ℕ => -1 * ((-x) ^ (n + 1) / ((n : ℝ) + 1)) + x ^ (n + 1) / (n + 1)
  have h_term_eq_goal :
      term ∘ (2 * ·) = fun k : ℕ => 2 * (1 / (2 * k + 1)) * x ^ (2 * k + 1) := by
    ext n
    dsimp only [term, (· ∘ ·)]
    rw [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)) x]
    push_cast
    ring_nf
  rw [← h_term_eq_goal, (mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff]
  · have h₁ := (hasSum_pow_div_log_of_abs_lt_one (Eq.trans_lt (abs_neg x) h)).mul_left (-1)
    convert h₁.add (hasSum_pow_div_log_of_abs_lt_one h) using 1
    ring_nf
  · intro m hm
    rw [range_two_mul, Set.mem_setOf_eq, ← Nat.even_add_one] at hm
    dsimp [term]
    rw [Even.neg_pow hm, neg_one_mul, neg_add_cancel]

theorem hasSum_log_one_add_inv {a : ℝ} (h : 0 < a) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1))
      (log (1 + a⁻¹)) := by
  have h₁ : |1 / (2 * a + 1)| < 1 := by
    rw [abs_of_pos, div_lt_one]
    · linarith
    · linarith
    · exact div_pos one_pos (by linarith)
  convert hasSum_log_sub_log_of_abs_lt_one h₁ using 1
  have h₂ : (2 : ℝ) * a + 1 ≠ 0 := by linarith
  have h₃ := h.ne'
  rw [← log_div]
  · congr
    field_simp
    linarith
  · field_simp
    linarith
  · field_simp

end Real
