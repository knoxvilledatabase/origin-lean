/-
Extracted from Analysis/BoxIntegral/Partition/Measure.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Box-additive functions defined by measures

In this file we prove a few simple facts about rectangular boxes, partitions, and measures:

- given a box `I : Box ι`, its coercion to `Set (ι → ℝ)` and `I.Icc` are measurable sets;
- if `μ` is a locally finite measure, then `(I : Set (ι → ℝ))` and `I.Icc` have finite measure;
- if `μ` is a locally finite measure, then `fun J ↦ μ.real J` is a box additive function.

For the last statement, we both prove it as a proposition and define a bundled
`BoxIntegral.BoxAdditiveMap` function.

## Tags

rectangular box, measure
-/

open Set

noncomputable section

open scoped ENNReal BoxIntegral

variable {ι : Type*}

namespace BoxIntegral

open MeasureTheory

namespace Box

variable (I : Box ι)

theorem measure_Icc_lt_top (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] : μ (Box.Icc I) < ∞ :=
  show μ (Icc I.lower I.upper) < ∞ from I.isCompact_Icc.measure_lt_top

theorem measure_coe_lt_top (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] : μ I < ∞ :=
  (measure_mono <| coe_subset_Icc).trans_lt (I.measure_Icc_lt_top μ)

section Countable

variable [Countable ι]

theorem measurableSet_coe : MeasurableSet (I : Set (ι → ℝ)) := by
  rw [coe_eq_pi]
  exact MeasurableSet.univ_pi fun i => measurableSet_Ioc

theorem measurableSet_Icc : MeasurableSet (Box.Icc I) :=
  _root_.measurableSet_Icc

theorem measurableSet_Ioo : MeasurableSet (Box.Ioo I) :=
  MeasurableSet.univ_pi fun _ => _root_.measurableSet_Ioo

end Countable

variable [Fintype ι]

theorem coe_ae_eq_Icc : (I : Set (ι → ℝ)) =ᵐ[volume] Box.Icc I := by
  rw [coe_eq_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

theorem Ioo_ae_eq_Icc : Box.Ioo I =ᵐ[volume] Box.Icc I :=
  Measure.univ_pi_Ioo_ae_eq_Icc

end Box

theorem Prepartition.measure_iUnion_toReal [Finite ι] {I : Box ι} (π : Prepartition I)
    (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] :
    μ.real π.iUnion = ∑ J ∈ π.boxes, μ.real J := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (fun J _ => (J.measure_coe_lt_top μ).ne), π.iUnion_def]
  simp only [← mem_boxes]
  rw [measure_biUnion_finset π.pairwiseDisjoint]
  exact fun J _ => J.measurableSet_coe

end BoxIntegral

open BoxIntegral BoxIntegral.Box

namespace MeasureTheory

namespace Measure
