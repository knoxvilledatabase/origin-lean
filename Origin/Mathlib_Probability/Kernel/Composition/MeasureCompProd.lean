/-
Extracted from Probability/Kernel/Composition/MeasureCompProd.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Composition-Product of a measure and a kernel

This operation, denoted by `⊗ₘ`, takes `μ : Measure α` and `κ : Kernel α β` and creates
`μ ⊗ₘ κ : Measure (α × β)`. The integral of a function against `μ ⊗ₘ κ` is
`∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ`.

`μ ⊗ₘ κ` is defined as `((Kernel.const Unit μ) ⊗ₖ (Kernel.prodMkLeft Unit κ)) ()`.

## Main definitions

* `Measure.compProd`: from `μ : Measure α` and `κ : Kernel α β`, get a `Measure (α × β)`.

## Notation

* `μ ⊗ₘ κ = μ.compProd κ`
-/

open scoped ENNReal

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

noncomputable

def compProd (μ : Measure α) (κ : Kernel α β) : Measure (α × β) :=
  (Kernel.const Unit μ ⊗ₖ Kernel.prodMkLeft Unit κ) ()
