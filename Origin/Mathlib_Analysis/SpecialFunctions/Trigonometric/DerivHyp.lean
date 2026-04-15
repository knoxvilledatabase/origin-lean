/-
Extracted from Analysis/SpecialFunctions/Trigonometric/DerivHyp.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Differentiability of hyperbolic trigonometric functions

## Main statements

The differentiability of the hyperbolic trigonometric functions is proved, and their derivatives are
computed.

## Tags

sinh, cosh, tanh
-/

noncomputable section

open scoped Asymptotics Topology Filter

open Set

namespace Complex

theorem hasStrictDerivAt_sinh (x : ℂ) : HasStrictDerivAt sinh (cosh x) x := by
  simp only [cosh, div_eq_mul_inv]
  convert ((hasStrictDerivAt_exp x).sub (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : ℂ)⁻¹
    using 1
  rw [id, mul_neg_one, sub_eq_add_neg, neg_neg]

theorem hasDerivAt_sinh (x : ℂ) : HasDerivAt sinh (cosh x) x :=
  (hasStrictDerivAt_sinh x).hasDerivAt

theorem isEquivalent_sinh : sinh ~[𝓝 0] id := by simpa using (hasDerivAt_sinh 0).isLittleO
