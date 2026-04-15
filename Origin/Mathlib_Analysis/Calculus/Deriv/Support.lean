/-
Extracted from Analysis/Calculus/Deriv/Support.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Support of the derivative of a function

In this file we prove that the (topological) support of a function includes the support of its
derivative. As a corollary, we show that the derivative of a function with compact support has
compact support.

## Keywords

derivative, support
-/

universe u v

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {f : 𝕜 → E}

/-! ### Support of derivatives -/

section Support

open Function

theorem support_deriv_subset : support (deriv f) ⊆ tsupport f := by
  intro x
  rw [← not_imp_not]
  intro h2x
  rw [not_mem_tsupport_iff_eventuallyEq] at h2x
  exact nmem_support.mpr (h2x.deriv_eq.trans (deriv_const x 0))

protected theorem HasCompactSupport.deriv (hf : HasCompactSupport f) :
    HasCompactSupport (deriv f) :=
  hf.mono' support_deriv_subset

end Support
