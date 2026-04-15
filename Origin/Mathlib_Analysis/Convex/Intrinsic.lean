/-
Extracted from Analysis/Convex/Intrinsic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Intrinsic frontier and interior

This file defines the intrinsic frontier, interior and closure of a set in a normed additive torsor.
These are also known as relative frontier, interior, closure.

The intrinsic frontier/interior/closure of a set `s` is the frontier/interior/closure of `s`
considered as a set in its affine span.

The intrinsic interior is in general greater than the topological interior, the intrinsic frontier
in general less than the topological frontier, and the intrinsic closure in cases of interest the
same as the topological closure.

## Definitions

* `intrinsicInterior`: Intrinsic interior
* `intrinsicFrontier`: Intrinsic frontier
* `intrinsicClosure`: Intrinsic closure

## Results

The main results are:
* `AffineIsometry.image_intrinsicInterior`/`AffineIsometry.image_intrinsicFrontier`/
  `AffineIsometry.image_intrinsicClosure`: Intrinsic interiors/frontiers/closures commute with
  taking the image under an affine isometry.
* `Set.Nonempty.intrinsicInterior`: The intrinsic interior of a nonempty convex set is nonempty.

## References

* Chapter 8 of [Barry Simon, *Convexity*][simon2011]
* Chapter 1 of [Rolf Schneider, *Convex Bodies: The Brunn-Minkowski theory*][schneider2013].

## TODO

* `IsClosed s → IsExtreme 𝕜 s (intrinsicFrontier 𝕜 s)`
* `x ∈ s → y ∈ intrinsicInterior 𝕜 s → openSegment 𝕜 x y ⊆ intrinsicInterior 𝕜 s`
-/

open AffineSubspace Set Topology

open scoped Pointwise

variable {𝕜 V W Q P : Type*}

section AddTorsor

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
  {s t : Set P} {x : P}

def intrinsicInterior (s : Set P) : Set P :=
  (↑) '' interior ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

def intrinsicFrontier (s : Set P) : Set P :=
  (↑) '' frontier ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

def intrinsicClosure (s : Set P) : Set P :=
  (↑) '' closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

variable {𝕜}
