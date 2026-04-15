/-
Extracted from Topology/UniformSpace/Equicontinuity.lean
Genuine: 14 of 14 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equicontinuity of a family of functions

Let `X` be a topological space and `α` a `UniformSpace`. A family of functions `F : ι → X → α`
is said to be *equicontinuous at a point `x₀ : X`* when, for any entourage `U` in `α`, there is a
neighborhood `V` of `x₀` such that, for all `x ∈ V`, and *for all `i`*, `F i x` is `U`-close to
`F i x₀`. In other words, one has `∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x, ∀ i, dist x₀ x < δ → dist (F i x₀) (F i x) < ε`.

`F` is said to be *equicontinuous* if it is equicontinuous at each point.

A closely related concept is that of ***uniform*** *equicontinuity* of a family of functions
`F : ι → β → α` between uniform spaces, which means that, for any entourage `U` in `α`, there is an
entourage `V` in `β` such that, if `x` and `y` are `V`-close, then *for all `i`*, `F i x` and
`F i y` are `U`-close. In other words, one has
`∀ U ∈ 𝓤 α, ∀ᶠ xy in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x y, ∀ i, dist x y < δ → dist (F i x₀) (F i x) < ε`.

## Main definitions

* `EquicontinuousAt`: equicontinuity of a family of functions at a point
* `Equicontinuous`: equicontinuity of a family of functions on the whole domain
* `UniformEquicontinuous`: uniform equicontinuity of a family of functions on the whole domain

We also introduce relative versions, namely `EquicontinuousWithinAt`, `EquicontinuousOn` and
`UniformEquicontinuousOn`, akin to `ContinuousWithinAt`, `ContinuousOn` and `UniformContinuousOn`
respectively.

## Main statements

* `equicontinuous_iff_continuous`: equicontinuity can be expressed as a simple continuity
  condition between well-chosen function spaces. This is really useful for building up the theory.
* `Equicontinuous.closure`: if a set of functions is equicontinuous, its closure
  *for the topology of pointwise convergence* is also equicontinuous.

## Notation

Throughout this file, we use :
- `ι`, `κ` for indexing types
- `X`, `Y`, `Z` for topological spaces
- `α`, `β`, `γ` for uniform spaces

## Implementation details

We choose to express equicontinuity as a properties of indexed families of functions rather
than sets of functions for the following reasons:
- it is really easy to express equicontinuity of `H : Set (X → α)` using our setup: it is just
  equicontinuity of the family `(↑) : ↥H → (X → α)`. On the other hand, going the other way around
  would require working with the range of the family, which is always annoying because it
  introduces useless existentials.
- in most applications, one doesn't work with bare functions but with a more specific hom type
  `hom`. Equicontinuity of a set `H : Set hom` would then have to be expressed as equicontinuity
  of `coe_fn '' H`, which is super annoying to work with. This is much simpler with families,
  because equicontinuity of a family `𝓕 : ι → hom` would simply be expressed as equicontinuity
  of `coe_fn ∘ 𝓕`, which doesn't introduce any nasty existentials.

To simplify statements, we do provide abbreviations `Set.EquicontinuousAt`, `Set.Equicontinuous`
and `Set.UniformEquicontinuous` asserting the corresponding fact about the family
`(↑) : ↥H → (X → α)` where `H : Set (X → α)`. Note however that these won't work for sets of hom
types, and in that case one should go back to the family definition rather than using `Set.image`.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]

## Tags

equicontinuity, uniform convergence, ascoli
-/

open UniformSpace Filter Set Uniformity Topology UniformConvergence Function

variable {ι κ X X' Y α α' β β' γ : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
  [uα : UniformSpace α] [uβ : UniformSpace β] [uγ : UniformSpace γ]

def EquicontinuousAt (F : ι → X → α) (x₀ : X) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U

protected abbrev Set.EquicontinuousAt (H : Set <| X → α) (x₀ : X) : Prop :=
  EquicontinuousAt ((↑) : H → X → α) x₀

def EquicontinuousWithinAt (F : ι → X → α) (S : Set X) (x₀ : X) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝[S] x₀, ∀ i, (F i x₀, F i x) ∈ U

protected abbrev Set.EquicontinuousWithinAt (H : Set <| X → α) (S : Set X) (x₀ : X) : Prop :=
  EquicontinuousWithinAt ((↑) : H → X → α) S x₀

def Equicontinuous (F : ι → X → α) : Prop :=
  ∀ x₀, EquicontinuousAt F x₀

protected abbrev Set.Equicontinuous (H : Set <| X → α) : Prop :=
  Equicontinuous ((↑) : H → X → α)

def EquicontinuousOn (F : ι → X → α) (S : Set X) : Prop :=
  ∀ x₀ ∈ S, EquicontinuousWithinAt F S x₀

protected abbrev Set.EquicontinuousOn (H : Set <| X → α) (S : Set X) : Prop :=
  EquicontinuousOn ((↑) : H → X → α) S

def UniformEquicontinuous (F : ι → β → α) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ xy : β × β in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U

protected abbrev Set.UniformEquicontinuous (H : Set <| β → α) : Prop :=
  UniformEquicontinuous ((↑) : H → β → α)

def UniformEquicontinuousOn (F : ι → β → α) (S : Set β) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), ∀ i, (F i xy.1, F i xy.2) ∈ U

protected abbrev Set.UniformEquicontinuousOn (H : Set <| β → α) (S : Set β) : Prop :=
  UniformEquicontinuousOn ((↑) : H → β → α) S

lemma EquicontinuousAt.equicontinuousWithinAt {F : ι → X → α} {x₀ : X} (H : EquicontinuousAt F x₀)
    (S : Set X) : EquicontinuousWithinAt F S x₀ :=
  fun U hU ↦ (H U hU).filter_mono inf_le_left

lemma EquicontinuousWithinAt.mono {F : ι → X → α} {x₀ : X} {S T : Set X}
    (H : EquicontinuousWithinAt F T x₀) (hST : S ⊆ T) : EquicontinuousWithinAt F S x₀ :=
  fun U hU ↦ (H U hU).filter_mono <| nhdsWithin_mono x₀ hST
