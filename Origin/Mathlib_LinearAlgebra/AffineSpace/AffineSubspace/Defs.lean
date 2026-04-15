/-
Extracted from LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Affine spaces

This file defines affine subspaces (over modules) and the affine span of a set of points.

## Main definitions

* `AffineSubspace k P` is the type of affine subspaces. Unlike affine spaces, affine subspaces are
  allowed to be empty, and lemmas that do not apply to empty affine subspaces have `Nonempty`
  hypotheses. There is a `CompleteLattice` structure on affine subspaces.
* `AffineSubspace.direction` gives the `Submodule` spanned by the pairwise differences of points
  in an `AffineSubspace`. There are various lemmas relating to the set of vectors in the
  `direction`, and relating the lattice structure on affine subspaces to that on their directions.
* `affineSpan` gives the affine subspace spanned by a set of points, with `vectorSpan` giving its
  direction. The `affineSpan` is defined in terms of `spanPoints`, which gives an explicit
  description of the points contained in the affine span; `spanPoints` itself should generally only
  be used when that description is required, with `affineSpan` being the main definition for other
  purposes. Two other descriptions of the affine span are proved equivalent: it is the `sInf` of
  affine subspaces containing the points, and (if `[Nontrivial k]`) it contains exactly those points
  that are affine combinations of points in the given set.

## Implementation notes

`outParam` is used in the definition of `AddTorsor V P` to make `V` an implicit argument (deduced
from `P`) in most cases. As for modules, `k` is an explicit argument rather than implied by `P` or
`V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `Analysis.Normed.Affine.AddTorsor` and
`Topology.Algebra.Affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

noncomputable section

open Affine

open Set

open scoped Pointwise

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AffineSpace V P]

def vectorSpan (s : Set P) : Submodule k V :=
  Submodule.span k (s -ᵥ s)

theorem vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ ⊆ s₂) : vectorSpan k s₁ ≤ vectorSpan k s₂ :=
  Submodule.span_mono (vsub_self_mono h)

variable (P) in
