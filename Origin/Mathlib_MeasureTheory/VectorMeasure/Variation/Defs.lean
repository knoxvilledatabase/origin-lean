/-
Extracted from MeasureTheory/VectorMeasure/Variation/Defs.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Total variation for vector-valued measures

This file contains the definition of variation for any `VectorMeasure` in an `ENormedAddCommMonoid`,
in particular, any `NormedAddCommGroup`.

Given a vector-valued measure `μ` we consider the problem of finding a countably additive function
`f` such that, for any set `E`, `‖μ(E)‖ ≤ f(E)`. This suggests defining `f(E)` as the supremum over
partitions `{Eᵢ}` of `E`, of the quantity `∑ᵢ, ‖μ(Eᵢ)‖`. Indeed any solution of the problem must be
not less than this function. It turns out that this function is a measure.

## Main definitions

* `VectorMeasure.variation`: the variation as a `Measure X`
* `VectorMeasure.ennrealVariation`: the variation as a `VectorMeasure X ℝ≥0∞`

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

variable {X : Type*} [MeasurableSpace X]

open MeasureTheory BigOperators NNReal ENNReal Function

namespace MeasureTheory.VectorMeasure

variable {V : Type*} [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

lemma isSigmaSubadditiveSetFun_enorm (μ : VectorMeasure X V) :
    IsSigmaSubadditiveSetFun (‖μ ·‖ₑ) := by
  intro s hs
  have hmeas : ∀ i, MeasurableSet (s i).val := fun i => (s i).prop
  simpa [VectorMeasure.of_disjoint_iUnion hmeas hs] using enorm_tsum_le_tsum_enorm

noncomputable def variation (μ : VectorMeasure X V) : Measure X :=
  preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp)

noncomputable def ennrealVariation (μ : VectorMeasure X V) : VectorMeasure X ℝ≥0∞ :=
  μ.variation.toENNRealVectorMeasure

end MeasureTheory.VectorMeasure
