/-
Extracted from Probability/Independence/Kernel/Indep.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Independence of families of sets with respect to a kernel and a measure

A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a kernel
`κ : Kernel α Ω` and a measure `μ` on `α` if for any finite set of indices `s = {i_1, ..., i_n}`,
for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then for `μ`-almost every `a : α`,
`κ a (⋂ i in s, f i) = ∏ i ∈ s, κ a (f i)`.

This notion of independence is a generalization of both independence and conditional independence.
For conditional independence, `κ` is the conditional kernel `ProbabilityTheory.condExpKernel` and
`μ` is the ambient measure. For (non-conditional) independence, `κ = Kernel.const Unit μ` and the
measure is the Dirac measure on `Unit`.

The main purpose of this file is to prove only once the properties that hold for both conditional
and non-conditional independence.

This file contains results about independence of families of sets and `σ`-algebras.
See the `IndepFun` file for results about independence of random variables.

## Main definitions

* `ProbabilityTheory.Kernel.iIndepSets`: independence of a family of sets of sets.
  Variant for two sets of sets: `ProbabilityTheory.Kernel.IndepSets`.
* `ProbabilityTheory.Kernel.iIndep`: independence of a family of σ-algebras. Variant for two
  σ-algebras: `Indep`.
* `ProbabilityTheory.Kernel.iIndepSet`: independence of a family of sets. Variant for two sets:
  `ProbabilityTheory.Kernel.IndepSet`.

See the file `Mathlib/Probability/Kernel/Basic.lean` for a more detailed discussion of these
definitions in the particular case of the usual independence notion.

## Main statements

* `ProbabilityTheory.Kernel.iIndepSets.iIndep`: if π-systems are independent as sets of sets,
  then the measurable space structures they generate are independent.
* `ProbabilityTheory.Kernel.IndepSets.Indep`: variant with two π-systems.
-/

open Set MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory.Kernel

variable {α Ω ι : Type*}

section Definitions

variable {_mα : MeasurableSpace α}

def iIndepSets {_mΩ : MeasurableSpace Ω}
    (π : ι → Set (Set Ω)) (κ : Kernel α Ω) (μ : Measure α := by volume_tac) : Prop :=
  ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
  ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i ∈ s, κ a (f i)

def IndepSets {_mΩ : MeasurableSpace Ω}
    (s1 s2 : Set (Set Ω)) (κ : Kernel α Ω) (μ : Measure α := by volume_tac) : Prop :=
  ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → (∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2)

def iIndep (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) κ μ

def Indep (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  IndepSets {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s} κ μ

def iIndepSet {_mΩ : MeasurableSpace Ω} (s : ι → Set Ω) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndep (m := fun i ↦ generateFrom {s i}) κ μ

def IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  Indep (generateFrom {s}) (generateFrom {t}) κ μ

end Definitions

section ByDefinition

variable {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
  {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α}
  {π : ι → Set (Set Ω)} {s : ι → Set Ω} {S : Finset ι} {f : ∀ x : ι, Ω → β x}
  {s1 s2 : Set (Set Ω)} {ι' : Type*} {g : ι' → ι}
