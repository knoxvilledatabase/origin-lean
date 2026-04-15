/-
Extracted from Analysis/SpecialFunctions/Complex/Arg.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# The argument of a complex number.

We define `arg : ℂ → ℝ`, returning a real number in the range $(-π, π]$,
such that for `x ≠ 0`, `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
while `arg 0` defaults to `0`
-/

open Filter Metric Set

open scoped ComplexConjugate Real Topology

namespace Complex

variable {a x z : ℂ}

noncomputable def arg (x : ℂ) : ℝ :=
  if 0 ≤ x.re then Real.arcsin (x.im / ‖x‖)
  else if 0 ≤ x.im then Real.arcsin ((-x).im / ‖x‖) + π else Real.arcsin ((-x).im / ‖x‖) - π

theorem sin_arg (x : ℂ) : Real.sin (arg x) = x.im / ‖x‖ := by
  unfold arg; split_ifs <;>
    simp [sub_eq_add_neg, Real.sin_arcsin (abs_le.1 (abs_im_div_norm_le_one x)).1
      (abs_le.1 (abs_im_div_norm_le_one x)).2, Real.sin_add, neg_div, Real.arcsin_neg, Real.sin_neg]

-- DISSOLVED: cos_arg
