/-
Extracted from MeasureTheory/Function/SpecialFunctions/Basic.lean
Genuine: 8 of 9 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Measurability of real and complex functions

We show that most standard real and complex functions are measurable, notably `exp`, `cos`, `sin`,
`cosh`, `sinh`, `log`, `pow`, `arcsin`, `arccos`.

See also `MeasureTheory.Function.SpecialFunctions.Arctan` and
`MeasureTheory.Function.SpecialFunctions.Inner`, which have been split off to minimize imports.
-/

assert_not_exists InnerProductSpace Real.arctan FiniteDimensional.proper

noncomputable section

open NNReal ENNReal MeasureTheory

namespace Real

variable {α : Type*} {_ : MeasurableSpace α} {f : α → ℝ} {μ : MeasureTheory.Measure α}

theorem measurable_exp : Measurable exp :=
  continuous_exp.measurable

theorem measurable_log : Measurable log :=
  measurable_of_measurable_on_compl_singleton 0 <|
    Continuous.measurable <| continuousOn_iff_continuous_restrict.1 continuousOn_log

lemma measurable_of_measurable_exp (hf : Measurable (fun x ↦ exp (f x))) :
    Measurable f := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp hf

lemma aemeasurable_of_aemeasurable_exp (hf : AEMeasurable (fun x ↦ exp (f x)) μ) :
    AEMeasurable f μ := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf

-- DISSOLVED: aemeasurable_of_aemeasurable_exp_mul

theorem measurable_sin : Measurable sin :=
  continuous_sin.measurable

theorem measurable_cos : Measurable cos :=
  continuous_cos.measurable

theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.measurable

theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.measurable
