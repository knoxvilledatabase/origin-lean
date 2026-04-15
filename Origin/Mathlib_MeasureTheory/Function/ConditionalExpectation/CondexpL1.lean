/-
Extracted from MeasureTheory/Function/ConditionalExpectation/CondexpL1.lean
Genuine: 21 of 21 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Conditional expectation in L1

This file contains two more steps of the construction of the conditional expectation, which is
completed in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`. See that file for a
description of the full process.

The conditional expectation of an `L²` function is defined in
`MeasureTheory.Function.ConditionalExpectation.CondexpL2`. In this file, we perform two steps.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `Set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).

## Main definitions

* `condExpL1`: Conditional expectation of a function as a linear map from `L1` to itself.

-/

noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α F F' G G' 𝕜 : Type*} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']
  -- G for a Lp add_subgroup
  [NormedAddCommGroup G]
  -- G' for integrals on a Lp add_subgroup
  [NormedAddCommGroup G']
  [NormedSpace ℝ G'] [CompleteSpace G']

section CondexpInd

/-! ## Conditional expectation of an indicator as a continuous linear map.

The goal of this section is to build
`condExpInd (hm : m ≤ m0) (μ : Measure α) (s : Set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/

variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α} [NormedSpace ℝ G]

section CondexpIndL1Fin

def condExpIndL1Fin (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : α →₁[μ] G :=
  (integrable_condExpIndSMul hm hs hμs x).toL1 _

theorem condExpIndL1Fin_ae_eq_condExpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condExpIndL1Fin hm hs hμs x =ᵐ[μ] condExpIndSMul hm hs hμs x :=
  (integrable_condExpIndSMul hm hs hμs x).coeFn_toL1

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

private theorem q {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {x : G} :
    MemLp (condExpIndSMul hm hs hμs x) 1 μ := by
  rw [memLp_one_iff_integrable]; apply integrable_condExpIndSMul

theorem condExpIndL1Fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condExpIndL1Fin hm hs hμs (x + y) =
    condExpIndL1Fin hm hs hμs x + condExpIndL1Fin hm hs hμs y := by
  ext1
  unfold condExpIndL1Fin Integrable.toL1
  grw [Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp, MemLp.coeFn_toLp, condExpIndSMul_add,
    Lp.coeFn_add]

theorem condExpIndL1Fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x := by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]

theorem condExpIndL1Fin_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x := by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]

theorem norm_condExpIndL1Fin_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ‖condExpIndL1Fin hm hs hμs x‖ ≤ μ.real s * ‖x‖ := by
  rw [L1.norm_eq_integral_norm, ← ENNReal.toReal_ofReal (norm_nonneg x), measureReal_def,
    ← ENNReal.toReal_mul,
    ← ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hμs ENNReal.ofReal_ne_top),
    ofReal_integral_norm_eq_lintegral_enorm]
  swap; · rw [← memLp_one_iff_integrable]; exact Lp.memLp _
  have h_eq :
    ∫⁻ a, ‖condExpIndL1Fin hm hs hμs x a‖ₑ ∂μ = ∫⁻ a, ‖condExpIndSMul hm hs hμs x a‖ₑ ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [condExpIndL1Fin_ae_eq_condExpIndSMul hm hs hμs x] with z hz
    rw [hz]
  rw [h_eq, ofReal_norm_eq_enorm]
  exact lintegral_nnnorm_condExpIndSMul_le hm hs hμs x

theorem condExpIndL1Fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condExpIndL1Fin hm (hs.union ht) ((measure_union_le s t).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne x =
    condExpIndL1Fin hm hs hμs x + condExpIndL1Fin hm ht hμt x := by
  ext1
  grw [Lp.coeFn_add, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndL1Fin_ae_eq_condExpIndSMul]
  rw [condExpIndSMul]
  rw [indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : ℝ)]
  rw [map_add]
  push_cast
  rw [map_add]
  grw [Lp.coeFn_add]
  rfl

end CondexpIndL1Fin

section CondexpIndL1

open scoped Classical in

def condExpIndL1 {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) (s : Set α)
    [SigmaFinite (μ.trim hm)] (x : G) : α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condExpIndL1Fin hm hs.1 hs.2 x else 0

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condExpIndL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : condExpIndL1 hm μ s x = condExpIndL1Fin hm hs hμs x := by
  simp only [condExpIndL1, And.intro hs hμs, dif_pos, Ne, not_false_iff, and_self_iff]

theorem condExpIndL1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condExpIndL1 hm μ s x = 0 := by
  simp only [condExpIndL1, hμs, not_true, Ne, dif_neg, not_false_iff,
    and_false]

theorem condExpIndL1_of_not_measurableSet (hs : ¬MeasurableSet s) (x : G) :
    condExpIndL1 hm μ s x = 0 := by
  simp only [condExpIndL1, hs, dif_neg, not_false_iff, false_and]

theorem condExpIndL1_add (x y : G) :
    condExpIndL1 hm μ s (x + y) = condExpIndL1 hm μ s x + condExpIndL1 hm μ s y := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [zero_add]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [zero_add]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_add hs hμs x y

theorem condExpIndL1_smul (c : ℝ) (x : G) :
    condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul hs hμs c x

theorem condExpIndL1_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul' hs hμs c x

theorem norm_condExpIndL1_le (x : G) : ‖condExpIndL1 hm μ s x‖ ≤ μ.real s * ‖x‖ := by
  by_cases hs : MeasurableSet s
  swap
  · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  by_cases hμs : μ s = ∞
  · rw [condExpIndL1_of_measure_eq_top hμs x, Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  · rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs x]
    exact norm_condExpIndL1Fin_le hs hμs x

theorem continuous_condExpIndL1 : Continuous fun x : G => condExpIndL1 hm μ s x :=
  continuous_of_linear_of_bound condExpIndL1_add condExpIndL1_smul norm_condExpIndL1_le

theorem condExpIndL1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condExpIndL1 hm μ (s ∪ t) x = condExpIndL1 hm μ s x + condExpIndL1 hm μ t x := by
  have hμst : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs x,
    condExpIndL1_of_measurableSet_of_measure_ne_top ht hμt x,
    condExpIndL1_of_measurableSet_of_measure_ne_top (hs.union ht) hμst x]
  exact condExpIndL1Fin_disjoint_union hs ht hμs hμt hst x

end CondexpIndL1

variable (G)

def condExpInd {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (s : Set α) : G →L[ℝ] α →₁[μ] G where
  toFun := condExpIndL1 hm μ s
  map_add' := condExpIndL1_add
  map_smul' := condExpIndL1_smul
  cont := continuous_condExpIndL1

variable {G}

theorem condExpInd_ae_eq_condExpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condExpInd G hm μ s x =ᵐ[μ] condExpIndSMul hm hs hμs x := by
  grw [← condExpIndL1Fin_ae_eq_condExpIndSMul]
  simp [condExpInd, condExpIndL1, hs, hμs]

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem aestronglyMeasurable_condExpInd (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AEStronglyMeasurable[m] (condExpInd G hm μ s x) μ :=
  (aestronglyMeasurable_condExpIndSMul hm hs hμs x).congr
    (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm
