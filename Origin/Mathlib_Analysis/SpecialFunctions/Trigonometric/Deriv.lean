/-
Extracted from Analysis/SpecialFunctions/Trigonometric/Deriv.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Differentiability of trigonometric functions

## Main statements

The differentiability of the usual trigonometric functions is proved, and their derivatives are
computed.

## Tags

sin, cos, tan, angle
-/

noncomputable section

open scoped Asymptotics Topology Filter

open Set

namespace Complex

theorem hasStrictDerivAt_sin (x : ℂ) : HasStrictDerivAt sin (cos x) x := by
  simp only [cos, div_eq_mul_inv]
  convert ((((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp.sub
    ((hasStrictDerivAt_id x).mul_const I).cexp).mul_const I).mul_const (2 : ℂ)⁻¹ using 1
  simp only [id]
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_neg, mul_one, one_mul, mul_assoc,
    I_mul_I, mul_neg_one, sub_neg_eq_add, add_comm]

theorem hasDerivAt_sin (x : ℂ) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt

theorem isEquivalent_sin : sin ~[𝓝 0] id := by simpa using (hasDerivAt_sin 0).isLittleO
