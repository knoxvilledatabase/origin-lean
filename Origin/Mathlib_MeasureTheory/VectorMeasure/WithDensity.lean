/-
Extracted from MeasureTheory/VectorMeasure/WithDensity.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Vector measure defined by an integral

Given a measure `μ` and an integrable function `f : α → E`, we can define a vector measure `v` such
that for all measurable sets `s`, `v s = ∫ x in s, f x ∂μ`. This definition is useful for
the Radon-Nikodym theorem for signed measures.

## Main definitions

* `MeasureTheory.Measure.withDensityᵥ`: the vector measure formed by integrating a function `f`
  with respect to a measure `μ` on some set if `f` is integrable, and `0` otherwise.

-/

noncomputable section

open scoped MeasureTheory NNReal ENNReal

variable {α : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

open TopologicalSpace

variable {μ : Measure α}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in

def Measure.withDensityᵥ {m : MeasurableSpace α} (μ : Measure α) (f : α → E) : VectorMeasure α E :=
  if hf : Integrable f μ then
    { measureOf' := fun s => if MeasurableSet s then ∫ x in s, f x ∂μ else 0
      empty' := by simp
      not_measurable' := fun _ hs => if_neg hs
      m_iUnion' := fun s hs₁ hs₂ => by
        convert hasSum_integral_iUnion hs₁ hs₂ hf.integrableOn with n
        · rw [if_pos (hs₁ n)]
        · rw [if_pos (MeasurableSet.iUnion hs₁)] }
  else 0

open Measure

variable {f g : α → E}

theorem withDensityᵥ_apply (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensityᵥ f s = ∫ x in s, f x ∂μ := by rw [withDensityᵥ, dif_pos hf]; exact dif_pos hs
