/-
Extracted from Analysis/Calculus/ContDiff/WithLp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivatives on `WithLp`
-/

open scoped ENNReal

section PiLp

open ContinuousLinearMap WithLp

variable {𝕜 ι : Type*} {E : ι → Type*} {H : Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup H] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [NormedSpace 𝕜 H] [Fintype ι] (p) [Fact (1 ≤ p)]
  {n : WithTop ℕ∞} {f : H → PiLp p E} {f' : H →L[𝕜] PiLp p E} {t : Set H} {y : H}

theorem contDiffWithinAt_piLp :
    ContDiffWithinAt 𝕜 n f t y ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffWithinAt_iff, contDiffWithinAt_pi]
  rfl
