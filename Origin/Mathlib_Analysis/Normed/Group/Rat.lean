/-
Extracted from Analysis/Normed/Group/Rat.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Analysis.Normed.Group.Int
import Mathlib.Topology.Instances.Rat

/-! # ℚ as a normed group -/

namespace Rat

instance instNormedAddCommGroup : NormedAddCommGroup ℚ where
  norm r := ‖(r : ℝ)‖
  dist_eq r₁ r₂ := by simp only [Rat.dist_eq, norm, Rat.cast_sub]

@[norm_cast, simp 1001]
theorem norm_cast_real (r : ℚ) : ‖(r : ℝ)‖ = ‖r‖ :=
  rfl

@[norm_cast, simp]
theorem _root_.Int.norm_cast_rat (m : ℤ) : ‖(m : ℚ)‖ = ‖m‖ := by
  rw [← Rat.norm_cast_real, ← Int.norm_cast_real]; congr 1

end Rat
