/-
Extracted from Analysis/SpecialFunctions/ExpDeriv.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Complex and real exponential

In this file we prove that `Complex.exp` and `Real.exp` are analytic functions.

## Tags

exp, derivative
-/

assert_not_exists IsConformalMap Conformal

noncomputable section

open Filter Asymptotics Set Function

open scoped Topology

/-! ## `Complex.exp` -/

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : E → ℂ} {z : ℂ} {x : E} {s : Set E}

theorem analyticOnNhd_cexp : AnalyticOnNhd ℂ exp univ := by
  rw [Complex.exp_eq_exp_ℂ]
  exact fun x _ ↦ NormedSpace.exp_analytic x

theorem analyticOn_cexp : AnalyticOn ℂ exp univ := analyticOnNhd_cexp.analyticOn
