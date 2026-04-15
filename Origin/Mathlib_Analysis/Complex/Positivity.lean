/-
Extracted from Analysis/Complex/Positivity.lean
Genuine: 2 | Conflates: 0 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Nonnegativity of values of holomorphic functions

We show that if `f` is holomorphic on an open disk `B(c,r)` and all iterated derivatives of `f`
at `c` are nonnegative real, then `f z ≥ 0` for all `z ≥ c` in the disk; see
`DifferentiableOn.nonneg_of_iteratedDeriv_nonneg`. We also provide a
variant `Differentiable.nonneg_of_iteratedDeriv_nonneg` for entire functions and versions
showing `f z ≥ f c` when all iterated derivatives except `f` itseld are nonnegative.
-/

open Complex

open scoped ComplexOrder

namespace DifferentiableOn

theorem nonneg_of_iteratedDeriv_nonneg {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (h : ∀ n, 0 ≤ iteratedDeriv n f c) ⦃z : ℂ⦄
    (hz₁ : c ≤ z) (hz₂ : z ∈ Metric.ball c r):
    0 ≤ f z := by
  have H := taylorSeries_eq_on_ball' hz₂ hf
  rw [← sub_nonneg] at hz₁
  have hz' := eq_re_of_ofReal_le hz₁
  rw [hz'] at hz₁ H
  refine H ▸ tsum_nonneg fun n ↦ ?_
  rw [← ofReal_natCast, ← ofReal_pow, ← ofReal_inv, eq_re_of_ofReal_le (h n), ← ofReal_mul,
    ← ofReal_mul]
  norm_cast at hz₁ ⊢
  have := zero_re ▸ (Complex.le_def.mp (h n)).1
  positivity

end DifferentiableOn

namespace Differentiable

theorem nonneg_of_iteratedDeriv_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ}
    (h : ∀ n, 0 ≤ iteratedDeriv n f c) ⦃z : ℂ⦄ (hz : c ≤ z) :
    0 ≤ f z := by
  refine hf.differentiableOn.nonneg_of_iteratedDeriv_nonneg (r := (z - c).re + 1) h hz ?_
  rw [← sub_nonneg] at hz
  rw [Metric.mem_ball, dist_eq, eq_re_of_ofReal_le hz]
  simpa only [Complex.abs_of_nonneg (nonneg_iff.mp hz).1] using lt_add_one _

-- DISSOLVED: apply_le_of_iteratedDeriv_nonneg

-- DISSOLVED: apply_le_of_iteratedDeriv_alternating

end Differentiable
