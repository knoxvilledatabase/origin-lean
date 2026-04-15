/-
Extracted from Probability/Kernel/Disintegration/Basic.lean
Genuine: 5 of 14 | Dissolved: 5 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Probability.Kernel.MeasureCompProd

/-!
# Disintegration of measures and kernels

This file defines predicates for a kernel to "disintegrate" a measure or a kernel. This kernel is
also called the "conditional kernel" of the measure or kernel.

A measure `ρ : Measure (α × Ω)` is disintegrated by a kernel `ρCond : Kernel α Ω` if
`ρ.fst ⊗ₘ ρCond = ρ`.

A kernel `ρ : Kernel α (β × Ω)` is disintegrated by a kernel `κCond : Kernel (α × β) Ω` if
`κ.fst ⊗ₖ κCond = κ`.

## Main definitions

* `MeasureTheory.Measure.IsCondKernel ρ ρCond`: Predicate for the kernel `ρCond` to disintegrate the
  measure `ρ`.
* `ProbabilityTheory.Kernel.IsCondKernel κ κCond`: Predicate for the kernel `κ Cond` to disintegrate
  the kernel `κ`.

Further, if `κ` is an s-finite kernel from a countable `α` such that each measure `κ a` is
disintegrated by some kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`.

## See also

`Mathlib.Probability.Kernel.Disintegration.StandardBorel` for a **construction** of disintegrating
kernels.
-/

open MeasureTheory Set Filter MeasurableSpace ProbabilityTheory

open scoped ENNReal MeasureTheory Topology

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mΩ : MeasurableSpace Ω}

/-!
### Disintegration of measures

This section provides a predicate for a kernel to disintegrate a measure.
-/

namespace MeasureTheory.Measure

variable (ρ : Measure (α × Ω)) (ρCond : Kernel α Ω)

class IsCondKernel : Prop where
  disintegrate : ρ.fst ⊗ₘ ρCond = ρ

variable [ρ.IsCondKernel ρCond]

lemma disintegrate : ρ.fst ⊗ₘ ρCond = ρ := IsCondKernel.disintegrate

-- DISSOLVED: IsCondKernel.isSFiniteKernel

variable [IsFiniteMeasure ρ]

-- DISSOLVED: IsCondKernel.apply_of_ne_zero_of_measurableSet

-- DISSOLVED: IsCondKernel.apply_of_ne_zero

-- DISSOLVED: IsCondKernel.isProbabilityMeasure

-- DISSOLVED: IsCondKernel.isMarkovKernel

end MeasureTheory.Measure

/-!
### Disintegration of kernels

This section provides a predicate for a kernel to disintegrate a kernel. It also proves that if `κ`
is an s-finite kernel from a countable `α` such that each measure `κ a` is disintegrated by some
kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`..
-/

namespace ProbabilityTheory.Kernel

variable (κ : Kernel α (β × Ω)) (κCond : Kernel (α × β) Ω)

/-! #### Predicate for a kernel to disintegrate a kernel -/

class IsCondKernel : Prop where
  protected disintegrate : κ.fst ⊗ₖ κCond = κ

instance instIsCondKernel_zero (κCond : Kernel (α × β) Ω) : IsCondKernel 0 κCond where
  disintegrate := by simp

variable [κ.IsCondKernel κCond]

lemma disintegrate : κ.fst ⊗ₖ κCond = κ := IsCondKernel.disintegrate

/-! #### Existence of a disintegrating kernel in a countable space -/

section Countable

variable [Countable α] (κCond : α → Kernel β Ω)

noncomputable def condKernelCountable (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y) :
    Kernel (α × β) Ω where
  toFun p := κCond p.1 p.2
  measurable' := by
    change Measurable ((fun q : β × α ↦ (κCond q.2) q.1) ∘ Prod.swap)
    refine (measurable_from_prod_countable' (fun a ↦ (κCond a).measurable) ?_).comp measurable_swap
    · intro x y hx hy
      simpa using DFunLike.congr (h_atom _ _ hy) rfl

lemma condKernelCountable_apply (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y)
    (p : α × β) : condKernelCountable κCond h_atom p = κCond p.1 p.2 := rfl

instance condKernelCountable.instIsMarkovKernel [∀ a, IsMarkovKernel (κCond a)]
     (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y) :
    IsMarkovKernel (condKernelCountable κCond h_atom) where
  isProbabilityMeasure p := (‹∀ a, IsMarkovKernel (κCond a)› p.1).isProbabilityMeasure p.2

instance condKernelCountable.instIsCondKernel [∀ a, IsMarkovKernel (κCond a)]
    (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y) (κ : Kernel α (β × Ω))
    [IsSFiniteKernel κ] [∀ a, (κ a).IsCondKernel (κCond a)] :
    κ.IsCondKernel (condKernelCountable κCond h_atom) := by
  constructor
  ext a s hs
  conv_rhs => rw [← (κ a).disintegrate (κCond a)]
  simp_rw [compProd_apply hs, condKernelCountable_apply, Measure.compProd_apply hs]
  congr

end Countable

end ProbabilityTheory.Kernel
