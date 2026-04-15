/-
Extracted from MeasureTheory/Measure/WithDensity.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Measure with a given density with respect to another measure

For a measure `μ` on `α` and a function `f : α → ℝ≥0∞`, we define a new measure `μ.withDensity f`.
On a measurable set `s`, that measure has value `∫⁻ a in s, f a ∂μ`.

An important result about `withDensity` is the Radon-Nikodym theorem. It states that, given measures
`μ, ν`, if `HaveLebesgueDecomposition μ ν` then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that
`μ = ν.withDensity f`.
See `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`.

-/

open Set hiding restrict restrict_apply

open Filter ENNReal NNReal MeasureTheory.Measure

namespace MeasureTheory

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}

noncomputable

def Measure.withDensity {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ a in s, f a ∂μ) (by simp) fun _ hs hd =>
    lintegral_iUnion hs hd _
