/-
Extracted from Topology/Instances/ENNReal/Lemmas.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topology on extended non-negative reals
-/

noncomputable section

open Filter Function Metric Set Topology

open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : ℝ≥0∞} {r : ℝ≥0} {x : ℝ≥0∞} {ε : ℝ≥0∞}

section TopologicalSpace

open TopologicalSpace

theorem isOpen_ne_top : IsOpen { a : ℝ≥0∞ | a ≠ ∞ } := isOpen_ne

theorem isOpen_Ico_zero : IsOpen (Ico 0 b) := by
  rw [ENNReal.Ico_eq_Iio]
  exact isOpen_Iio

theorem coe_range_mem_nhds : range ((↑) : ℝ≥0 → ℝ≥0∞) ∈ 𝓝 (r : ℝ≥0∞) :=
  IsOpen.mem_nhds isOpenEmbedding_coe.isOpen_range <| mem_range_self _
