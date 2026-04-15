/-
Extracted from Probability/Kernel/Composition/ParallelComp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Parallel composition of kernels

Two kernels `κ : Kernel α β` and `η : Kernel γ δ` can be applied in parallel to give a kernel
`κ ∥ₖ η` from `α × γ` to `β × δ`: `(κ ∥ₖ η) (a, c) = (κ a).prod (η c)`.

## Main definitions

* `parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ)`: parallel composition
  of two s-finite kernels. We define a notation `κ ∥ₖ η = parallelComp κ η`.
  `∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b, ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1`

## Notation

* `κ ∥ₖ η = ProbabilityTheory.Kernel.parallelComp κ η`

-/

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {κ : Kernel α β} {η : Kernel γ δ} {x : α × γ}

open Classical in

noncomputable

irreducible_def parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ) :=
  if h : IsSFiniteKernel κ ∧ IsSFiniteKernel η then
  { toFun := fun x ↦ (κ x.1).prod (η x.2)
    measurable' := by
      have hκ := h.1
      have hη := h.2
      refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
      simp_rw [Measure.prod_apply hs]
      refine Measurable.lintegral_kernel_prod_right'
        (f := fun y ↦ prodMkLeft α η y.1 (Prod.mk y.2 ⁻¹' s)) (κ := prodMkRight γ κ) ?_
      have : (fun y ↦ prodMkLeft α η y.1 (Prod.mk y.2 ⁻¹' s))
          = fun y ↦ prodMkRight β (prodMkLeft α η) y (Prod.mk y.2 ⁻¹' s) := rfl
      rw [this]
      exact measurable_kernel_prodMk_left (measurable_fst.snd.prodMk measurable_snd hs) }
  else 0
