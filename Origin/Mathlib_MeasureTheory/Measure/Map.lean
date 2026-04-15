/-
Extracted from MeasureTheory/Measure/Map.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pushforward of a measure

In this file we define the pushforward `MeasureTheory.Measure.map f μ`
of a measure `μ` along an almost everywhere measurable map `f`.
If `f` is not a.e. measurable, then we define `map f μ` to be zero.

## Main definitions

* `MeasureTheory.Measure.map f μ`: map of the measure `μ` along the map `f`.

## Main statements

* `map_apply`: for `s` a measurable set, `μ.map f s = μ (f ⁻¹' s)`
* `map_map`: `(μ.map f).map g = μ.map (g ∘ f)`

-/

variable {α β γ : Type*}

open Set Function ENNReal NNReal

open Filter hiding map

namespace MeasureTheory

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {s : Set α}

namespace Measure

noncomputable

def liftLinear [MeasurableSpace β] (f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β)
    (hf : ∀ μ : Measure α, ‹_› ≤ (f μ.toOuterMeasure).caratheodory) :
    Measure α →ₗ[ℝ≥0∞] Measure β where
  toFun μ := (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by
    simp only [map_add, coe_add, Pi.add_apply, toMeasure_apply, add_toOuterMeasure,
      OuterMeasure.coe_add, hs]
  map_smul' c μ := ext fun s hs => by
    simp only [map_smulₛₗ, Pi.smul_apply, toMeasure_apply, smul_toOuterMeasure (R := ℝ≥0∞),
      OuterMeasure.coe_smul (R := ℝ≥0∞), smul_apply, hs]

lemma liftLinear_apply₀ {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : NullMeasurableSet s (liftLinear f hf μ)) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply₀ _ (hf μ) hs
