/-
Extracted from Analysis/Convex/Visible.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Points in sight

This file defines the relation of visibility with respect to a set, and lower bounds how many
elements of a set a point sees in terms of the dimension of that set.

## TODO

The art gallery problem can be stated using the visibility predicate: A set `A` (the art gallery) is
guarded by a finite set `G` (the guards) iff `∀ a ∈ A, ∃ g ∈ G, IsVisible ℝ sᶜ a g`.
-/

open AffineMap Filter Finset Set

open scoped Cardinal Pointwise Topology

variable {𝕜 V P : Type*}

section AddTorsor

variable [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
  {s t : Set P} {x y z : P}

omit [IsOrderedRing 𝕜] in

variable (𝕜) in

def IsVisible (s : Set P) (x y : P) : Prop := ∀ ⦃z⦄, z ∈ s → ¬ Sbtw 𝕜 x z y
