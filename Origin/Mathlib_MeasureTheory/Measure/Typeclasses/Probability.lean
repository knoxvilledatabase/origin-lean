/-
Extracted from MeasureTheory/Measure/Typeclasses/Probability.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Classes for probability measures

We introduce the following typeclasses for measures:

* `IsZeroOrProbabilityMeasure μ`: `μ univ = 0 ∨ μ univ = 1`;
* `IsProbabilityMeasure μ`: `μ univ = 1`.
-/

namespace MeasureTheory

open Set Measure Filter Function ENNReal

variable {α β : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {s : Set α}

section IsZeroOrProbabilityMeasure

class IsZeroOrProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 0 ∨ μ univ = 1

lemma isZeroOrProbabilityMeasure_iff : IsZeroOrProbabilityMeasure μ ↔ μ univ = 0 ∨ μ univ = 1 :=
  ⟨fun _ ↦ IsZeroOrProbabilityMeasure.measure_univ, IsZeroOrProbabilityMeasure.mk⟩

lemma prob_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} : μ s ≤ 1 := by
  apply (measure_mono (subset_univ _)).trans
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h <;> simp [h]

lemma measureReal_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} :
    μ.real s ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one.symm ▸ prob_le_one)
