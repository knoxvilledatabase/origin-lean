/-
Extracted from Probability/Kernel/Composition/Prod.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Product and composition of kernels

We define the product `κ ×ₖ η` of s-finite kernels `κ : Kernel α β` and `η : Kernel α γ`, which is
a kernel from `α` to `β × γ`.

## Main definitions

* `prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ)`: product of 2 s-finite kernels.
  `∫⁻ bc, f bc ∂((κ ×ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η a) ∂(κ a)`

## Main statements

* `lintegral_prod`: Lebesgue integral of a function against a product of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by product.

## Notation

* `κ ×ₖ η = ProbabilityTheory.Kernel.prod κ η`

-/

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

noncomputable def prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ) :=
  (κ ∥ₖ η) ∘ₖ copy α
