/-
Extracted from MeasureTheory/Function/LpSeminorm/LpNorm.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Real-valued Lᵖ norm

This file proves theorems about `MeasureTheory.lpNorm`,
a real-valued version of `MeasureTheory.eLpNorm`.
-/

open Filter

open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] {f g h : α → E}

lemma toReal_eLpNorm (hf : AEStronglyMeasurable f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ := by
  rw [lpNorm, if_pos hf]

lemma ofReal_lpNorm (hf : MemLp f p μ) : .ofReal (lpNorm f p μ) = eLpNorm f p μ := by
  rw [← toReal_eLpNorm hf.aestronglyMeasurable, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
