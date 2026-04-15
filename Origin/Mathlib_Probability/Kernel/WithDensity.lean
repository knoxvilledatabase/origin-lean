/-
Extracted from Probability/Kernel/WithDensity.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# With Density

For an s-finite kernel `κ : Kernel α β` and a function `f : α → β → ℝ≥0∞` which is finite
everywhere, we define `withDensity κ f` as the kernel `a ↦ (κ a).withDensity (f a)`. This is
an s-finite kernel.

## Main definitions

* `ProbabilityTheory.Kernel.withDensity κ (f : α → β → ℝ≥0∞)`:
  kernel `a ↦ (κ a).withDensity (f a)`. It is defined if `κ` is s-finite. If `f` is finite
  everywhere, then this is also an s-finite kernel. The class of s-finite kernels is the smallest
  class of kernels that contains finite kernels and which is stable by `withDensity`.
  Integral: `∫⁻ b, g b ∂(withDensity κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

## Main statements

* `ProbabilityTheory.Kernel.lintegral_withDensity`:
  `∫⁻ b, g b ∂(withDensity κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

-/

open MeasureTheory ProbabilityTheory

open scoped MeasureTheory ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

variable {κ : Kernel α β} {f : α → β → ℝ≥0∞}

noncomputable def withDensity (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → β → ℝ≥0∞) :
    Kernel α β :=
  @dite _ (Measurable (Function.uncurry f)) (Classical.dec _) (fun hf =>
    (⟨fun a => (κ a).withDensity (f a),
      by
        refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
        simp_rw [withDensity_apply _ hs]
        exact hf.setLIntegral_kernel_prod_right hs⟩ : Kernel α β)) fun _ => 0

theorem withDensity_of_not_measurable (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : ¬Measurable (Function.uncurry f)) : withDensity κ f = 0 := by classical exact dif_neg hf

protected theorem withDensity_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) :
    withDensity κ f a = (κ a).withDensity (f a) := by
  classical
  rw [withDensity, dif_pos hf]
  rfl

protected theorem withDensity_apply' (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) (s : Set β) :
    withDensity κ f a s = ∫⁻ b in s, f a b ∂κ a := by
  rw [Kernel.withDensity_apply κ hf, withDensity_apply' _ s]

nonrec lemma withDensity_congr_ae (κ : Kernel α β) [IsSFiniteKernel κ] {f g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfg : ∀ a, f a =ᵐ[κ a] g a) :
    withDensity κ f = withDensity κ g := by
  ext a
  rw [Kernel.withDensity_apply _ hf, Kernel.withDensity_apply _ hg, withDensity_congr_ae (hfg a)]

nonrec lemma withDensity_absolutelyContinuous [IsSFiniteKernel κ]
    (f : α → β → ℝ≥0∞) (a : α) :
    Kernel.withDensity κ f a ≪ κ a := by
  by_cases hf : Measurable (Function.uncurry f)
  · rw [Kernel.withDensity_apply _ hf]
    exact withDensity_absolutelyContinuous _ _
  · rw [withDensity_of_not_measurable _ hf]
    simp [Measure.AbsolutelyContinuous.zero]
