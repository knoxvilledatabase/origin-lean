/-
Extracted from Topology/Convenient/ContinuousMapGeneratedBy.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `X`-continuous maps

Given a family `X i` of topological spaces, we introduce a predicate
`ContinuousGeneratedBy X` on maps `g : Y ⟶ Z` saying that
`g` is `X`-continuous, i.e. for any continuous map `f : X i → Y`,
the composition `g ∘ f` is continuous.

## References
* [Martín Escardó, Jimmie Lawson and Alex Simpson, *Comparing Cartesian closed
  categories of (core) compactly generated spaces*][escardo-lawson-simpson-2004]

-/

universe v v' t u

open Topology

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

namespace Topology

variable (X) in

def ContinuousGeneratedBy (g : Y → Z) : Prop :=
  ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f)

lemma continuousGeneratedBy_iff (g : Y → Z) :
    ContinuousGeneratedBy X g ↔
      Continuous ((WithGeneratedByTopology.equiv (X := X)).symm ∘ g ∘
        WithGeneratedByTopology.equiv (X := X)) := by
  rw [IsGeneratedBy.equiv_symm_comp_continuous_iff,
    WithGeneratedByTopology.continuous_from_iff]
  rfl

def ContinuousGeneratedBy.continuousMap {g : Y → Z}
    (hg : ContinuousGeneratedBy X g) :
    C(WithGeneratedByTopology X Y, WithGeneratedByTopology X Z) :=
  ⟨WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv, by
    rwa [← continuousGeneratedBy_iff]⟩
