/-
Extracted from Analysis/Distribution/SchwartzSpace/Deriv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivatives of Schwartz functions

In this file we define the various notions of derivatives of Schwartz functions.

## Main definitions

* `SchwartzMap.fderivCLM`: The differential as a continuous linear map
  `𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)`
* `SchwartzMap.derivCLM`: The one-dimensional derivative as a continuous linear map
  `𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F)`
* `SchwartzMap.instLineDeriv`: The directional derivative with notation `∂_{m} f`
* `SchwartzMap.instLaplacian`: The Laplacian for `𝓢(E, F)` as an instance of the notation type-class
  `Laplacian`.

## Main statements

* `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`: the iterated directional derivative is given
  by the applied Fréchet derivative of a Schwartz function.
* `SchwartzMap.laplacian_eq_sum`: the Laplacian is given by the sum of second derivatives in any
  orthonormal basis.
* `SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left`: Integration by parts using the
  directional derivative `∂_{m}`
* `SchwartzMap.integral_bilinear_laplacian_right_eq_left`: Integration by parts for the Laplacian

-/

variable {ι 𝕜 𝕜' D E F V F F₁ F₂ F₃ : Type*}

namespace SchwartzMap

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]

section Derivatives

/-! ### Derivatives of Schwartz functions -/

variable [NormedSpace ℝ E]

variable (𝕜)

variable [RCLike 𝕜] [NormedSpace 𝕜 F]

variable (F) in

def derivCLM : 𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F) :=
  mkCLM (deriv ·) (fun f g _ => deriv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => deriv_const_smul a f.differentiableAt)
    (fun f => (contDiff_succ_iff_deriv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [Real.norm_eq_abs, Finset.sup_singleton, schwartzSeminormFamily_apply, one_mul,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ'] using
        f.le_seminorm' 𝕜 k (n + 1) x⟩
