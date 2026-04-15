/-
Extracted from AlgebraicTopology/SimplicialSet/PiZero.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Connected components of simplicial sets

In this file, we define the type `π₀ X` of connected components
of a simplicial sets. We also introduce typeclasses
`IsPreconnected X` and `IsConnected X`.

## TODO

* Define the subcomplex of `X` corresponding to an element in `π₀ X` (@joelriou)
* Show `π₀ X` is a coequalizer of the two face maps `X _⦋1⦌ → X _⦋0⦌` (@joelriou)
* Show `π₀ X` identifies to the colimit of `X` as a functor to types

## References:

- [Kerodon 00G5: Connected Components of Simplicial Sets](https://kerodon.net/tag/00G5)

-/

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable {X Y Z : SSet.{u}}

def π₀Rel (x₀ x₁ : X _⦋0⦌) : Prop :=
  Nonempty (Edge x₀ x₁)

variable (X) in

def π₀ : Type u := Quot (π₀Rel (X := X))

attribute [irreducible] π₀

namespace π₀

unseal π₀ in

def mk : X _⦋0⦌ → π₀ X := Quot.mk _

unseal π₀ in

lemma mk_surjective : Function.Surjective (π₀.mk (X := X)) := Quot.mk_surjective

unseal π₀ in

lemma sound {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    π₀.mk x₀ = π₀.mk x₁ :=
  Quot.sound ⟨e⟩

unseal π₀ in

lemma mk_eq_mk_iff (x₀ x₁ : X _⦋0⦌) :
    π₀.mk x₀ = π₀.mk x₁ ↔ Relation.EqvGen π₀Rel x₀ x₁ :=
  Quot.eq
