/-
Extracted from Probability/Kernel/Basic.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Basic kernels

This file contains basic results about kernels in general and definitions of some particular
kernels.

## Main definitions

* `ProbabilityTheory.Kernel.deterministic (f : α → β) (hf : Measurable f)`:
  kernel `a ↦ Measure.dirac (f a)`.
* `ProbabilityTheory.Kernel.id`: the identity kernel, deterministic kernel for
  the identity function.
* `ProbabilityTheory.Kernel.copy α`: the deterministic kernel that maps `x : α` to
  the Dirac measure at `(x, x) : α × α`.
* `ProbabilityTheory.Kernel.discard α`: the Markov kernel to the type `PUnit`.
* `ProbabilityTheory.Kernel.swap α β`: the deterministic kernel that maps `(x, y)` to
  the Dirac measure at `(y, x)`.
* `ProbabilityTheory.Kernel.const α (μβ : measure β)`: constant kernel `a ↦ μβ`.
* `ProbabilityTheory.Kernel.restrict κ (hs : MeasurableSet s)`: kernel for which the image of
  `a : α` is `(κ a).restrict s`.
  Integral: `∫⁻ b, f b ∂(κ.restrict hs a) = ∫⁻ b in s, f b ∂(κ a)`
* `ProbabilityTheory.Kernel.comapRight`: Kernel with value `(κ a).comap f`,
  for a measurable embedding `f`. That is, for a measurable set `t : Set β`,
  `ProbabilityTheory.Kernel.comapRight κ hf a t = κ a (f '' t)`
* `ProbabilityTheory.Kernel.piecewise (hs : MeasurableSet s) κ η`: the kernel equal to `κ`
  on the measurable set `s` and to `η` on its complement.

## Main statements

-/

assert_not_exists MeasureTheory.integral

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Kernel α β}

namespace Kernel

section Deterministic

noncomputable def deterministic (f : α → β) (hf : Measurable f) : Kernel α β where
  toFun a := Measure.dirac (f a)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.dirac_apply' _ hs]
    exact measurable_one.indicator (hf hs)

theorem deterministic_apply' {f : α → β} (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) : deterministic f hf a s = s.indicator (fun _ => 1) (f a) := by
  rw [deterministic]
  change Measure.dirac (f a) s = s.indicator 1 (f a)
  simp_rw [Measure.dirac_apply' _ hs]

theorem deterministic_congr {f g : α → β} {hf : Measurable f} (h : f = g) :
    deterministic f hf = deterministic g (h ▸ hf) := by
  grind

-- INSTANCE (free from Core): isMarkovKernel_deterministic

theorem lintegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    (hf : Measurable f) : ∫⁻ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, lintegral_dirac' _ hf]
