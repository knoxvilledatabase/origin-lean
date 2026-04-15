/-
Extracted from Probability/Kernel/Disintegration/Basic.lean
Genuine: 6 of 15 | Dissolved: 5 | Infrastructure: 4
-/
import Origin.Core

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

`Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean` for a **construction** of
disintegrating kernels.
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
`ProbabilityTheory.Kernel.condKernelCountable`.
-/

namespace ProbabilityTheory.Kernel

variable (κ : Kernel α (β × Ω)) (κCond : Kernel (α × β) Ω)

/-! #### Predicate for a kernel to disintegrate a kernel -/

class IsCondKernel : Prop where
  protected disintegrate : κ.fst ⊗ₖ κCond = κ

-- INSTANCE (free from Core): instIsCondKernel_zero

lemma disintegrate [κ.IsCondKernel κCond] : κ.fst ⊗ₖ κCond = κ := IsCondKernel.disintegrate

lemma IsCondKernel.isProbabilityMeasure_ae [IsFiniteKernel κ.fst] [κ.IsCondKernel κCond] (a : α) :
    ∀ᵐ b ∂(κ.fst a), IsProbabilityMeasure (κCond (a, b)) := by
  have h := disintegrate κ κCond
  by_cases h_sfin : IsSFiniteKernel κCond
  swap; · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h_sfin] at h; simp [h.symm]
  suffices ∀ᵐ b ∂(κ.fst a), κCond (a, b) Set.univ = 1 by
    convert this with b
    exact ⟨fun _ ↦ measure_univ, fun h ↦ ⟨h⟩⟩
  suffices (∀ᵐ b ∂(κ.fst a), κCond (a, b) Set.univ ≤ 1)
      ∧ (∀ᵐ b ∂(κ.fst a), 1 ≤ κCond (a, b) Set.univ) by
    filter_upwards [this.1, this.2] with b h1 h2 using le_antisymm h1 h2
  have h_eq s (hs : MeasurableSet s) :
      ∫⁻ b, s.indicator (fun b ↦ κCond (a, b) Set.univ) b ∂κ.fst a = κ.fst a s := by
    conv_rhs => rw [← h]
    rw [fst_compProd_apply _ _ _ hs]
  have h_meas : Measurable fun b ↦ κCond (a, b) Set.univ :=
    (κCond.measurable_coe MeasurableSet.univ).comp measurable_prodMk_left
  constructor
  · rw [ae_le_const_iff_forall_gt_measure_zero]
    intro r hr
    let s := {b | r ≤ κCond (a, b) Set.univ}
    have hs : MeasurableSet s := h_meas measurableSet_Ici
    have h_2_le : s.indicator (fun _ ↦ r) ≤ s.indicator (fun b ↦ (κCond (a, b)) Set.univ) := by
      intro b
      by_cases hbs : b ∈ s
      · simpa [hbs]
      · simp [hbs]
    have : ∫⁻ b, s.indicator (fun _ ↦ r) b ∂(κ.fst a) ≤ κ.fst a s :=
      (lintegral_mono h_2_le).trans_eq (h_eq s hs)
    rw [lintegral_indicator_const hs] at this
    contrapose! this with h_ne_zero
    conv_lhs => rw [← one_mul (κ.fst a s)]
    gcongr
    finiteness
  · rw [ae_const_le_iff_forall_lt_measure_zero]
    intro r hr
    let s := {b | κCond (a, b) Set.univ ≤ r}
    have hs : MeasurableSet s := h_meas measurableSet_Iic
    have h_2_le : s.indicator (fun b ↦ (κCond (a, b)) Set.univ) ≤ s.indicator (fun _ ↦ r) := by
      intro b
      by_cases hbs : b ∈ s
      · simpa [hbs]
      · simp [hbs]
    have : κ.fst a s ≤ ∫⁻ b, s.indicator (fun _ ↦ r) b ∂(κ.fst a) :=
      (h_eq s hs).symm.trans_le (lintegral_mono h_2_le)
    rw [lintegral_indicator_const hs] at this
    contrapose! this with h_ne_zero
    conv_rhs => rw [← one_mul (κ.fst a s)]
    gcongr
    finiteness

/-! #### Existence of a disintegrating kernel in a countable space -/

section Countable

variable [Countable α] (κCond : α → Kernel β Ω)

noncomputable def condKernelCountable (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y) :
    Kernel (α × β) Ω where
  toFun p := κCond p.1 p.2
  measurable' := by
    refine measurable_from_prod_countable_right' (fun a ↦ (κCond a).measurable) fun x y hx hy ↦ ?_
    simpa using DFunLike.congr (h_atom _ _ hy) rfl

-- INSTANCE (free from Core): condKernelCountable.instIsMarkovKernel

-- INSTANCE (free from Core): condKernelCountable.instIsCondKernel

end Countable

end ProbabilityTheory.Kernel
