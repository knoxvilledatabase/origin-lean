/-
Extracted from MeasureTheory/Measure/PreVariation.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pre-variation of a subadditive set function

Given a σ-subadditive `ℝ≥0∞`-valued set function `f`, we define the pre-variation as the supremum
over finite measurable partitions of the sum of `f` on the parts. This construction yields a
measure.

## Main definitions

* `IsSigmaSubadditiveSetFun f`: `f` is σ-subadditive on measurable sets
* `ennrealPreVariation f`: the `VectorMeasure X ℝ≥0∞` built from a σ-subadditive function
* `preVariation f`: the `Measure X` built from a σ-subadditive function

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

variable {X : Type*} [MeasurableSpace X]

open MeasureTheory BigOperators NNReal ENNReal Function

namespace MeasureTheory

/-!
## Pre-variation of a subadditive `ℝ≥0∞`-valued function

Given a set function `f : Set X → ℝ≥0∞` we can define another set function by taking the supremum
over all finite partitions of measurable sets `E i` of the sum of `∑ i, f (E i)`. If `f` is
σ-subadditive then the function defined is an `ℝ≥0∞`-valued measure.
-/

variable (f : Set X → ℝ≥0∞)

open Classical in

noncomputable def preVariationFun (s : Set X) : ℝ≥0∞ :=
  if h : MeasurableSet s then
    ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p ∈ P.parts, f p
  else 0

end

namespace preVariation

variable (f : Set X → ℝ≥0∞)

lemma empty : preVariationFun f ∅ = 0 := by simp [preVariationFun]
