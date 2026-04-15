/-
Extracted from MeasureTheory/Measure/Doubling.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Uniformly locally doubling measures

A uniformly locally doubling measure `μ` on a metric space is a measure for which there exists a
constant `C` such that for all sufficiently small radii `ε`, and for any centre, the measure of a
ball of radius `2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

This file records basic facts about uniformly locally doubling measures.

## Main definitions

  * `IsUnifLocDoublingMeasure`: the definition of a uniformly locally doubling measure (as a
    typeclass).
  * `IsUnifLocDoublingMeasure.doublingConstant`: a function yielding the doubling constant `C`
    appearing in the definition of a uniformly locally doubling measure.
-/

assert_not_exists Real.instPow

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace ENNReal NNReal Topology

class IsUnifLocDoublingMeasure {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
  (μ : Measure α) : Prop where
  exists_measure_closedBall_le_mul'' :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ C * μ (closedBall x ε)

namespace IsUnifLocDoublingMeasure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ]

theorem exists_measure_closedBall_le_mul :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ C * μ (closedBall x ε) :=
  exists_measure_closedBall_le_mul''

def doublingConstant : ℝ≥0 :=
  Classical.choose <| exists_measure_closedBall_le_mul μ

theorem eventually_measure_le_doublingConstant_mul :
    ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ doublingConstant μ * μ (closedBall x ε) :=
  Classical.choose_spec <| exists_measure_closedBall_le_mul μ
