/-
Extracted from Probability/Independence/Kernel/IndepFun.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Independence of random variables with respect to a kernel and a measure

A family of random variables is independent if the corresponding `σ`-algebras are independent.
Independence of families of sets and `σ`-algebras is covered in the `Indep` file.
This file deals with independence of random variables specifically.

Note that we define independence with respect to a kernel and a measure. This notion of independence
is a generalization of both independence and conditional independence.
For conditional independence, `κ` is the conditional kernel `ProbabilityTheory.condExpKernel` and
`μ` is the ambient measure. For (non-conditional) independence, `κ = Kernel.const Unit μ` and the
measure is the Dirac measure on `Unit`.

## Main definition

* `ProbabilityTheory.Kernel.iIndepFun`: independence of a family of functions (random variables).
  Variant for two functions: `ProbabilityTheory.Kernel.IndepFun`.
-/

open Set MeasureTheory MeasurableSpace

namespace ProbabilityTheory.Kernel

variable {α Ω ι β β' γ γ' : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}

section Definitions

def iIndepFun {β : ι → Type*} [m : ∀ x : ι, MeasurableSpace (β x)]
    (f : ∀ x : ι, Ω → β x) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndep (m := fun x ↦ MeasurableSpace.comap (f x) (m x)) κ μ

def IndepFun [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) κ μ

end Definitions

section ByDefinition

variable {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
  {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α}
  {π : ι → Set (Set Ω)} {s : ι → Set Ω} {S : Finset ι} {f : ∀ x : ι, Ω → β x}
  {s1 s2 : Set (Set Ω)} {ι' : Type*} {g : ι' → ι}
