/-
Extracted from Analysis/SpecialFunctions/Complex/LogDeriv.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Differentiability of the complex `log` function

-/

assert_not_exists IsConformalMap Conformal

open Set Filter

open scoped Real Topology

namespace Complex

theorem isOpenMap_exp : IsOpenMap exp :=
  isOpenMap_of_hasStrictDerivAt hasStrictDerivAt_exp exp_ne_zero

theorem hasStrictDerivAt_log {x : ℂ} (h : x ∈ slitPlane) : HasStrictDerivAt log x⁻¹ x :=
  have h0 : x ≠ 0 := slitPlane_ne_zero h
  expOpenPartialHomeomorph.hasStrictDerivAt_symm h h0 <| by
    simpa [exp_log h0] using hasStrictDerivAt_exp (log x)

lemma hasDerivAt_log {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt log z⁻¹ z :=
  HasStrictDerivAt.hasDerivAt <| hasStrictDerivAt_log hz
