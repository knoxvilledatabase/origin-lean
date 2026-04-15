/-
Extracted from MeasureTheory/Function/LpSeminorm/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic theorems about ℒp space
-/

noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology ComplexConjugate

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

section Top

theorem MemLp.eLpNorm_lt_top [TopologicalSpace ε] {f : α → ε} (hfp : MemLp f p μ) :
    eLpNorm f p μ < ∞ :=
  hfp.2
