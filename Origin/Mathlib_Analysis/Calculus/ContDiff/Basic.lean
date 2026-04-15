/-
Extracted from Analysis/Calculus/ContDiff/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Basic properties of continuously-differentiable functions

This file continues the development of the API for `ContDiff`, `ContDiffAt`, etc, covering
constants, products, composition with linear maps, etc.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open Set Fin Filter Function

open scoped Topology ContDiff

-- INSTANCE (free from Core): 1001]

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s t : Set E} {f : E → F} {x : E} {b : E × F → G} {m n : WithTop ℕ∞}
  {p : E → FormalMultilinearSeries 𝕜 E F}

/-! ### Constants -/

section constants

theorem iteratedFDerivWithin_succ_const (n : ℕ) (c : F) :
    iteratedFDerivWithin 𝕜 (n + 1) (fun _ : E ↦ c) s = 0 := by
  induction n with
  | zero =>
    ext1
    simp [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp, comp_def]
  | succ n IH =>
    rw [iteratedFDerivWithin_succ_eq_comp_left, IH]
    simp only [Pi.zero_def, comp_def, fderivWithin_fun_const, map_zero]
