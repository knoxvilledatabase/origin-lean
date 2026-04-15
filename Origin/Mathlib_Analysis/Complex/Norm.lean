/-
Extracted from Analysis/Complex/Norm.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
  # Norm on the complex numbers
-/

noncomputable section

open ComplexConjugate Topology Filter Set

namespace Complex

variable {z : ℂ}

-- INSTANCE (free from Core): instNorm

theorem norm_mul_self_eq_normSq (z : ℂ) : ‖z‖ * ‖z‖ = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)

protected theorem norm_nonneg (z : ℂ) : 0 ≤ ‖z‖ :=
  Real.sqrt_nonneg _
