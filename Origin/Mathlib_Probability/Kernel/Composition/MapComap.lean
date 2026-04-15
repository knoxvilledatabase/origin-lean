/-
Extracted from Probability/Kernel/Composition/MapComap.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Map of a kernel by a measurable function

We define the map and comap of a kernel along a measurable function, as well as some often useful
particular cases.

## Main definitions

Kernels built from other kernels:
* `map (κ : Kernel α β) (f : β → γ) : Kernel α γ`
  `∫⁻ c, g c ∂(map κ f a) = ∫⁻ b, g (f b) ∂(κ a)`
* `comap (κ : Kernel α β) (f : γ → α) (hf : Measurable f) : Kernel γ β`
  `∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c))`

## Main statements

* `lintegral_map`, `lintegral_comap`: Lebesgue integral of a function against the map or comap of
  a kernel.

-/

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

section MapComap

/-! ### map, comap -/

variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : β → γ} {g : γ → α}

noncomputable def mapOfMeasurable (κ : Kernel α β) (f : β → γ) (hf : Measurable f) :
    Kernel α γ where
  toFun a := (κ a).map f
  measurable' := by fun_prop

open Classical in

noncomputable def map [MeasurableSpace γ] (κ : Kernel α β) (f : β → γ) : Kernel α γ :=
  if hf : Measurable f then mapOfMeasurable κ f hf else 0

theorem map_of_not_measurable (κ : Kernel α β) {f : β → γ} (hf : ¬(Measurable f)) :
    map κ f = 0 := by
  simp [map, hf]
