/-
Extracted from MeasureTheory/Integral/Indicator.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

noncomputable section

/-!
# Results about indicator functions, their integrals, and measures

This file has a few measure theoretic or integration-related results on indicator functions.

## Implementation notes

This file exists to avoid importing `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`
in `Mathlib.MeasureTheory.Integral.Lebesgue`.

## TODO

The result `MeasureTheory.tendsto_measure_of_tendsto_indicator` here could be proved without
integration, if we had convergence of measures results for countably generated filters. Ideally,
the present file would then become unnecessary: lemmas such as
`MeasureTheory.tendsto_measure_of_ae_tendsto_indicator` would not need integration so could be
moved out of `Mathlib.MeasureTheory.Integral.Lebesgue`, and the lemmas in this file could be
moved to, e.g., `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`.

-/

namespace MeasureTheory

section TendstoIndicator

open Filter ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {A : Set α}

variable {ι : Type*} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

lemma tendsto_measure_of_tendsto_indicator {μ : Measure α}
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : ∀ x, ∀ᶠ i in L, x ∈ As i ↔ x ∈ A) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  rcases L.eq_or_neBot with rfl | _
  · exact tendsto_bot
  apply tendsto_measure_of_ae_tendsto_indicator L ?_ As_mble B_mble B_finmeas As_le_B
        (ae_of_all μ h_lim)
  exact measurableSet_of_tendsto_indicator L As_mble h_lim

lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
    (μ : Measure α) [IsFiniteMeasure μ] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : ∀ x, ∀ᶠ i in L, x ∈ As i ↔ x ∈ A) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  rcases L.eq_or_neBot with rfl | _
  · exact tendsto_bot
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L ?_ As_mble (ae_of_all μ h_lim)
  exact measurableSet_of_tendsto_indicator L As_mble h_lim

end TendstoIndicator -- section

end MeasureTheory
