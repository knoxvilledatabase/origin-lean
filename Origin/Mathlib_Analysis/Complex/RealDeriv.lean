/-
Extracted from Analysis/Complex/RealDeriv.lean
Genuine: 9 of 12 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-! # Real differentiability of complex-differentiable functions

`HasDerivAt.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.
-/

assert_not_exists IsConformalMap Conformal

section RealDerivOfComplex

/-! ### Differentiability of the restriction to `ℝ` of complex functions -/

open Complex

variable {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in

theorem ContDiff.real_of_complex {n : WithTop ℕ∞} (h : ContDiff ℂ n e) :
    ContDiff ℝ n fun x : ℝ => (e x).re :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.real_of_complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

set_option backward.isDefEq.respectTransparency false in

theorem HasStrictDerivAt.complexToReal_fderiv' {f : ℂ → E} {x : ℂ} {f' : E}
    (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasStrictFDerivAt.restrictScalars ℝ

set_option backward.isDefEq.respectTransparency false in

theorem HasDerivAt.complexToReal_fderiv' {f : ℂ → E} {x : ℂ} {f' : E} (h : HasDerivAt f f' x) :
    HasFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasFDerivAt.restrictScalars ℝ

set_option backward.isDefEq.respectTransparency false in

theorem HasDerivWithinAt.complexToReal_fderiv' {f : ℂ → E} {s : Set ℂ} {x : ℂ} {f' : E}
    (h : HasDerivWithinAt f f' s x) :
    HasFDerivWithinAt f (reCLM.smulRight f' + I • imCLM.smulRight f') s x := by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasFDerivWithinAt.restrictScalars ℝ

set_option backward.isDefEq.respectTransparency false in

theorem HasStrictDerivAt.complexToReal_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasStrictFDerivAt.restrictScalars ℝ

set_option backward.isDefEq.respectTransparency false in

theorem HasDerivAt.complexToReal_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasDerivAt f f' x) :
    HasFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasFDerivAt.restrictScalars ℝ

set_option backward.isDefEq.respectTransparency false in

theorem HasDerivWithinAt.complexToReal_fderiv {f : ℂ → ℂ} {s : Set ℂ} {f' x : ℂ}
    (h : HasDerivWithinAt f f' s x) : HasFDerivWithinAt f (f' • (1 : ℂ →L[ℝ] ℂ)) s x := by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasFDerivWithinAt.restrictScalars ℝ

theorem HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z) : HasDerivAt (fun y : ℝ => e ↑y) e' z := by
  simpa only [ofRealCLM_apply, ofReal_one, mul_one] using hf.comp z ofRealCLM.hasDerivAt

set_option backward.isDefEq.respectTransparency false in

theorem HasDerivAt.ofReal_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivAt f u z) :
    HasDerivAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u z := by
  simpa only [ofRealCLM_apply, ofReal_one, real_smul, mul_one] using
    ofRealCLM.hasDerivAt.scomp z hf

end RealDerivOfComplex
