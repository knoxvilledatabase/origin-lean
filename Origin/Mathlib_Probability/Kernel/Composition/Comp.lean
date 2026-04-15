/-
Extracted from Probability/Kernel/Composition/Comp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Composition of kernels

We define the composition `η ∘ₖ κ` of kernels `κ : Kernel α β` and `η : Kernel β γ`, which is
a kernel from `α` to `γ`.

## Main definitions

* `comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ`: composition of 2 kernels.
  We define a notation `η ∘ₖ κ = comp η κ`.
  `∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a)`
* The monoid structure on `Kernel α α` given by kernel composition.

## Main statements

* `lintegral_comp`: Lebesgue integral of a function against a composition of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by composition.
* `pow_add_apply_eq_lintegral`: Chapman-Kolmogorov equations.

## Notation

* `η ∘ₖ κ = ProbabilityTheory.Kernel.comp η κ`

-/

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

noncomputable def comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ where
  toFun a := (κ a).bind η
  measurable' := (Measure.measurable_bind' η.measurable).comp κ.measurable
