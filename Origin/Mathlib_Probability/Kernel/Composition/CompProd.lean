/-
Extracted from Probability/Kernel/Composition/CompProd.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Composition-product of kernels

We define the composition-product `κ ⊗ₖ η` of two s-finite kernels `κ : Kernel α β` and
`η : Kernel (α × β) γ`, a kernel from `α` to `β × γ`.

A note on names:
The composition-product `Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)` is named composition in
[kallenberg2021] and product on the wikipedia article on transition kernels.
Most papers studying categories of kernels call composition the map we call composition. We adopt
that convention because it fits better with the use of the name `comp` elsewhere in mathlib.

## Main definitions

* `compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ)`: composition-product of 2
  s-finite kernels. We define a notation `κ ⊗ₖ η = compProd κ η`.
  `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`

## Main statements

* `lintegral_compProd`: Lebesgue integral of a function against a composition-product of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by composition-product.

## Notation

* `κ ⊗ₖ η = ProbabilityTheory.Kernel.compProd κ η`

-/

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

section CompositionProduct

/-!
### Composition-Product of kernels

We define a kernel composition-product
`compProd : Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)`.
-/

variable {s : Set (β × γ)}

noncomputable irreducible_def compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ) :=
  swap γ β ∘ₖ (η ∥ₖ Kernel.id)
    ∘ₖ deterministic MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _)
    ∘ₖ (Kernel.id ∥ₖ copy β) ∘ₖ (Kernel.id ∥ₖ κ) ∘ₖ copy α
