/-
Extracted from Probability/Kernel/Composition/MeasureComp.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about the composition of a measure and a kernel

Basic lemmas about the composition `κ ∘ₘ μ` of a kernel `κ` and a measure `μ`.

-/

open scoped ENNReal

open ProbabilityTheory MeasureTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

lemma comp_assoc {η : Kernel β γ} : η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ :=
  Measure.bind_bind κ.aemeasurable η.aemeasurable

lemma comp_eq_comp_const_apply : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) () := by
  rw [Kernel.comp_apply, Kernel.const_apply]

lemma comp_eq_sum_of_countable [Countable α] [MeasurableSingletonClass α] :
    κ ∘ₘ μ = Measure.sum (fun ω ↦ μ {ω} • κ ω) := by
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.bind_apply hs (by fun_prop)]
  simp [lintegral_countable', mul_comm]
