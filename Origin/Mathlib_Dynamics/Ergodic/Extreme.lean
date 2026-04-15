/-
Extracted from Dynamics/Ergodic/Extreme.lean
Genuine: 7 of 9 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Ergodic measures as extreme points

In this file we prove that a finite measure `μ` is an ergodic measure for a self-map `f`
iff it is an extreme point of the set of invariant measures of `f` with the same total volume.
We also specialize this result to probability measures.
-/

open Filter Set Function MeasureTheory Measure ProbabilityTheory

open scoped NNReal ENNReal Topology

variable {X : Type*} {m : MeasurableSpace X} {μ ν : Measure X} {f : X → X}

namespace Ergodic

theorem of_mem_extremePoints
    (h : μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}) :
    Ergodic f μ :=
  .of_mem_extremePoints_measure_univ_eq ENNReal.one_ne_top <| by
    simpa only [isProbabilityMeasure_iff] using h

theorem eq_of_absolutelyContinuous_measure_univ_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) (huniv : ν univ = μ univ) :
    ν = μ := by
  rcases hμ.eq_smul_of_absolutelyContinuous hfν hνμ with ⟨c, rfl⟩
  rcases eq_or_ne μ 0 with rfl | hμ₀
  · simp
  · simp_all [ENNReal.mul_eq_right]

theorem eq_of_absolutelyContinuous [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ν = μ :=
  eq_of_absolutelyContinuous_measure_univ_eq hμ hfν hνμ <| by simp

theorem mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] (hμ : Ergodic f μ) :
    μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ} := by
  rw [mem_extremePoints_iff_left]
  refine ⟨⟨hμ.toMeasurePreserving, rfl⟩, ?_⟩
  rintro ν₁ ⟨hfν₁, hν₁μ⟩ ν₂ ⟨hfν₂, hν₂μ⟩ ⟨a, b, ha, hb, hab, rfl⟩
  have : IsFiniteMeasure ν₁ := ⟨by rw [hν₁μ]; apply measure_lt_top⟩
  apply hμ.eq_of_absolutelyContinuous_measure_univ_eq hfν₁ (.add_right _ _) hν₁μ
  apply absolutelyContinuous_smul ha.ne'

theorem mem_extremePoints [IsProbabilityMeasure μ] (hμ : Ergodic f μ) :
    μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} := by
  simpa only [isProbabilityMeasure_iff, measure_univ] using hμ.mem_extremePoints_measure_univ_eq

theorem iff_mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] :
    Ergodic f μ ↔ μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ} :=
  ⟨mem_extremePoints_measure_univ_eq, of_mem_extremePoints_measure_univ_eq (measure_ne_top _ _)⟩

theorem iff_mem_extremePoints [IsProbabilityMeasure μ] :
    Ergodic f μ ↔ μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} :=
  ⟨mem_extremePoints, of_mem_extremePoints⟩

end Ergodic
