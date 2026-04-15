/-
Extracted from Probability/Independence/Basic.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → MeasurableSpace Ω` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `MeasurableSpace.comap f m`.

## Main statements

* `iIndepSets.iIndep`: if π-systems are independent as sets of sets, then the
  measurable space structures they generate are independent.
* `IndepSets.indep`: variant with two π-systems.

## Notation

* `X ⟂ᵢ[μ] Y` for `IndepFun X Y μ`, independence of two random variables.
* `X ⟂ᵢ Y` for `IndepFun X Y volume`.

These notations are scoped in the `ProbabilityTheory` namespace.

## Implementation notes

The definitions of independence in this file are a particular case of independence with respect to a
kernel and a measure, as defined in the file `Kernel.lean`.

We provide four definitions of independence:
* `iIndepSets`: independence of a family of sets of sets `pi : ι → Set (Set Ω)`. This is meant to
  be used with π-systems.
* `iIndep`: independence of a family of measurable space structures `m : ι → MeasurableSpace Ω`,
* `iIndepSet`: independence of a family of sets `s : ι → Set Ω`,
* `iIndepFun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), MeasurableSpace (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without the starting `i`, for example `IndepFun` is the version of `iIndepFun`
for two functions.

The definition of independence for `iIndepSets` uses finite sets (`Finset`). See
`ProbabilityTheory.Kernel.iIndepSets`. An alternative and equivalent way of defining independence
would have been to use countable sets.

Most of the definitions and lemmas in this file list all variables instead of using the `variable`
keyword at the beginning of a section, for example
`lemma Indep.symm {Ω} {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {μ : measure Ω} ...` .
This is intentional, to be able to control the order of the `MeasurableSpace` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`{_mΩ : MeasurableSpace Ω}`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
  Part A, Chapter 4.
-/

assert_not_exists MeasureTheory.Integrable

open MeasureTheory MeasurableSpace Set

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι β γ : Type*} {κ : ι → Type*}

section Definitions

def iIndepSets {_mΩ : MeasurableSpace Ω}
    (π : ι → Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepSets π (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

def IndepSets {_mΩ : MeasurableSpace Ω}
    (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepSets s1 s2 (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

def iIndep (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) :
    Prop :=
  Kernel.iIndep m (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

def Indep (m₁ m₂ : MeasurableSpace Ω)
    {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.Indep m₁ m₂ (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

def iIndepSet {_mΩ : MeasurableSpace Ω} (s : ι → Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepSet s (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

def IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepSet s t (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

def iIndepFun {_mΩ : MeasurableSpace Ω} {β : ι → Type*} [m : ∀ x : ι, MeasurableSpace (β x)]
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepFun f (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

def IndepFun {β γ} {_mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepFun f g (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

end Definitions
