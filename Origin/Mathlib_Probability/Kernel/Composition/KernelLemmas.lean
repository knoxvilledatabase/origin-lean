/-
Extracted from Probability/Kernel/Composition/KernelLemmas.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas relating different ways to compose kernels

This file contains lemmas about the composition of kernels that involve several types of
compositions/products.

## Main statements

* `comp_eq_snd_compProd`: `η ∘ₖ κ = snd (κ ⊗ₖ prodMkLeft X η)`
* `parallelComp_comp_parallelComp`: `(η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ')`
* `deterministic_comp_copy`: for a deterministic kernel, copying then applying the kernel to
  the two copies is the same as first applying the kernel then copying. That is, if `κ` is
  a deterministic kernel, `(κ ∥ₖ κ) ∘ₖ copy X = copy Y ∘ₖ κ`.

-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {X Y Z T : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z} {mT : MeasurableSpace T}
  {μ : Measure X} {ν : Measure Y} {κ : Kernel X Y} {η : Kernel Z T}

namespace ProbabilityTheory.Kernel

theorem comp_eq_snd_compProd (η : Kernel Y Z) [IsSFiniteKernel η] (κ : Kernel X Y)
    [IsSFiniteKernel κ] : η ∘ₖ κ = snd (κ ⊗ₖ prodMkLeft X η) := by
  ext a s hs
  rw [comp_apply' _ _ _ hs, snd_apply' _ _ hs, compProd_apply (measurable_snd hs)]
  simp [← Set.preimage_comp]
