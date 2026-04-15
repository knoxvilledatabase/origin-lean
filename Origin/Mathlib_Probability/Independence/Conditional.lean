/-
Extracted from Probability/Independence/Conditional.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conditional Independence

We define conditional independence of sets/σ-algebras/functions with respect to a σ-algebra.

Two σ-algebras `m₁` and `m₂` are conditionally independent given a third σ-algebra `m'` if for all
`m₁`-measurable sets `t₁` and `m₂`-measurable sets `t₂`,
`μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`.

On standard Borel spaces, the conditional expectation with respect to `m'` defines a kernel
`ProbabilityTheory.condExpKernel`, and the definition above is equivalent to
`∀ᵐ ω ∂μ, condExpKernel μ m' ω (t₁ ∩ t₂) = condExpKernel μ m' ω t₁ * condExpKernel μ m' ω t₂`.
We use this property as the definition of conditional independence.

## Main definitions

We provide four definitions of conditional independence:
* `iCondIndepSets`: conditional independence of a family of sets of sets `pi : ι → Set (Set Ω)`.
  This is meant to be used with π-systems.
* `iCondIndep`: conditional independence of a family of measurable space structures
  `m : ι → MeasurableSpace Ω`,
* `iCondIndepSet`: conditional independence of a family of sets `s : ι → Set Ω`,
* `iCondIndepFun`: conditional independence of a family of functions. For measurable spaces
  `m : Π (i : ι), MeasurableSpace (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without the starting `i`, for example `CondIndepFun` is the version of
`iCondIndepFun` for two functions.

## Main statements

* `ProbabilityTheory.iCondIndepSets.iCondIndep`: if π-systems are conditionally independent as sets
  of sets, then the measurable space structures they generate are conditionally independent.
* `ProbabilityTheory.condIndepSets.condIndep`: variant with two π-systems.

## Notation

* `X ⟂ᵢ[Z, hZ; μ] Y` for `CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ`,
  independence of `X` and `Y` given `Z`.
* `X ⟂ᵢ[Z, hZ] Y` for the cases of `μ = volume`.

These notations are scoped in the `ProbabilityTheory` namespace.

## Implementation notes

The definitions of conditional independence in this file are a particular case of independence with
respect to a kernel and a measure, as defined in the file
`Mathlib/Probability/Independence/Kernel.lean`.
The kernel used is `ProbabilityTheory.condExpKernel`.

-/

open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

section Definitions

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] (hm' : m' ≤ mΩ)

def iCondIndepSets (π : ι → Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] :
    Prop :=
  Kernel.iIndepSets π (condExpKernel μ m') (μ.trim hm')

def CondIndepSets (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] :
    Prop :=
  Kernel.IndepSets s1 s2 (condExpKernel μ m') (μ.trim hm')

def iCondIndep (m : ι → MeasurableSpace Ω)
    (μ : @Measure Ω mΩ := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndep m (condExpKernel (mΩ := mΩ) μ m') (μ.trim hm')

end

def CondIndep (m' m₁ m₂ : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hm' : m' ≤ mΩ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.Indep m₁ m₂ (condExpKernel μ m') (μ.trim hm')

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  (hm' : m' ≤ mΩ)

def iCondIndepSet (s : ι → Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndepSet s (condExpKernel μ m') (μ.trim hm')

def CondIndepSet (s t : Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.IndepSet s t (condExpKernel μ m') (μ.trim hm')

def iCondIndepFun {β : ι → Type*} [m : ∀ x : ι, MeasurableSpace (β x)]
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndepFun f (condExpKernel μ m') (μ.trim hm')

def CondIndepFun {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.IndepFun f g (condExpKernel μ m') (μ.trim hm')

end

end Definitions
