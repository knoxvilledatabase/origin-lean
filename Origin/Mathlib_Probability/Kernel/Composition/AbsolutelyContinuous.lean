/-
Extracted from Probability/Kernel/Composition/AbsolutelyContinuous.lean
Genuine: 4 of 6 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# Absolute continuity of the composition of measures and kernels

This file contains some results about the absolute continuity of the composition of measures and
kernels which use an assumption `CountableOrCountablyGenerated α β` on the measurable spaces.

Results that hold without that assumption are in files about the definitions of compositions and
products, like `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` and
`Mathlib/Probability/Kernel/Composition/MeasureComp.lean`.

The assumption ensures the measurability of the sets where two kernels are absolutely continuous
or mutually singular.

## Main statements

* `absolutelyContinuous_compProd_iff'`: `μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a`.

-/

open ProbabilityTheory Filter

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} [IsFiniteKernel κ] [IsFiniteKernel η]
  [MeasurableSpace.CountableOrCountablyGenerated α β]

lemma MutuallySingular.compProd_of_right' (μ ν : Measure α) (hκη : ∀ᵐ a ∂ν, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  refine (MutuallySingular.compProd_of_right _ _ ?_).symm
  simp_rw [MutuallySingular.comm, hκη]

lemma mutuallySingular_compProd_right_iff [SFinite μ] :
    μ ⊗ₘ κ ⟂ₘ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ⟂ₘ η a :=
  ⟨fun h ↦ mutuallySingular_of_mutuallySingular_compProd h AbsolutelyContinuous.rfl
    AbsolutelyContinuous.rfl, MutuallySingular.compProd_of_right _ _⟩

lemma AbsolutelyContinuous.kernel_of_compProd [SFinite μ] (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    ∀ᵐ a ∂μ, κ a ≪ η a := by
  suffices ∀ᵐ a ∂μ, κ.singularPart η a = 0 by
    filter_upwards [this] with a ha
    rwa [Kernel.singularPart_eq_zero_iff_absolutelyContinuous] at ha
  rw [← κ.rnDeriv_add_singularPart η, compProd_add_right, AbsolutelyContinuous.add_left_iff] at h
  have : μ ⊗ₘ κ.singularPart η ⟂ₘ ν ⊗ₘ η :=
    MutuallySingular.compProd_of_right μ ν (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  refine compProd_eq_zero_iff.mp ?_
  exact eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2 this

-- DISSOLVED: absolutelyContinuous_compProd_iff'

lemma absolutelyContinuous_compProd_right_iff [SFinite μ] :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ≪ η a :=
  ⟨AbsolutelyContinuous.kernel_of_compProd, AbsolutelyContinuous.compProd_right⟩

end MeasureTheory.Measure
