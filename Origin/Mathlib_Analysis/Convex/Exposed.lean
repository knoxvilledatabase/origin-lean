/-
Extracted from Analysis/Convex/Exposed.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exposed sets

This file defines exposed sets and exposed points for sets in a real vector space.

An exposed subset of `A` is a subset of `A` that is the set of all maximal points of a functional
(a continuous linear map `E → 𝕜`) over `A`. By convention, `∅` is an exposed subset of all sets.
This allows for better functoriality of the definition (the intersection of two exposed subsets is
exposed, faces of a polytope form a bounded lattice).
This is an analytic notion of "being on the side of". It is stronger than being extreme (see
`IsExposed.isExtreme`), but weaker (for exposed points) than being a vertex.

An exposed set of `A` is sometimes called a "face of `A`", but we decided to reserve this
terminology to the more specific notion of a face of a polytope (sometimes hopefully soon out
on mathlib!).

## Main declarations

* `IsExposed 𝕜 A B`: States that `B` is an exposed set of `A` (in the literature, `A` is often
  implicit).
* `IsExposed.isExtreme`: An exposed set is also extreme.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Prove lemmas relating exposed sets and points to the intrinsic frontier.
-/

open Affine Set

section PreorderSemiring

variable (𝕜 : Type*) {E : Type*} [TopologicalSpace 𝕜] [Semiring 𝕜] [Preorder 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {A B : Set E}

def IsExposed (A B : Set E) : Prop :=
  B.Nonempty → ∃ l : StrongDual 𝕜 E, B = { x ∈ A | ∀ y ∈ A, l y ≤ l x }

end PreorderSemiring

section OrderedRing

variable {𝕜 : Type*} {E : Type*} [TopologicalSpace 𝕜] [Ring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {l : StrongDual 𝕜 E} {A B C : Set E} {x : E}

def ContinuousLinearMap.toExposed (l : StrongDual 𝕜 E) (A : Set E) : Set E :=
  { x ∈ A | ∀ y ∈ A, l y ≤ l x }

theorem ContinuousLinearMap.toExposed.isExposed : IsExposed 𝕜 A (l.toExposed A) := fun _ => ⟨l, rfl⟩

theorem isExposed_empty : IsExposed 𝕜 A ∅ := fun ⟨_, hx⟩ => by
  exfalso
  exact hx

namespace IsExposed

protected theorem subset (hAB : IsExposed 𝕜 A B) : B ⊆ A := by
  rintro x hx
  obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩
  exact hx.1
