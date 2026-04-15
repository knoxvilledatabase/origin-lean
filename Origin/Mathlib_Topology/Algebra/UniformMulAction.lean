/-
Extracted from Topology/Algebra/UniformMulAction.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Multiplicative action on the completion of a uniform space

In this file we define typeclasses `UniformContinuousConstVAdd` and
`UniformContinuousConstSMul` and prove that a multiplicative action on `X` with uniformly
continuous `(•) c` can be extended to a multiplicative action on `UniformSpace.Completion X`.

In later files once the additive group structure is set up, we provide
* `UniformSpace.Completion.DistribMulAction`
* `UniformSpace.Completion.MulActionWithZero`
* `UniformSpace.Completion.Module`

TODO: Generalise the results here from the concrete `Completion` to any `AbstractCompletion`.
-/

universe u v w x y

open scoped Uniformity

noncomputable section

variable (R : Type u) (M : Type v) (N : Type w) (X : Type x) (Y : Type y) [UniformSpace X]
  [UniformSpace Y]

class UniformContinuousConstVAdd [VAdd M X] : Prop where
  uniformContinuous_const_vadd : ∀ c : M, UniformContinuous (c +ᵥ · : X → X)
