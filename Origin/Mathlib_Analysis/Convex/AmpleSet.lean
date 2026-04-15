/-
Extracted from Analysis/Convex/AmpleSet.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ample subsets of real vector spaces

In this file we study ample sets in real vector spaces. A set is ample if all its connected
component have full convex hull. Ample sets are an important ingredient for defining ample
differential relations.

## Main results
- `ampleSet_empty` and `ampleSet_univ`: the empty set and `univ` are ample
- `AmpleSet.union`: the union of two ample sets is ample
- `AmpleSet.{pre}image`: being ample is invariant under continuous affine equivalences;
  `AmpleSet.{pre}image_iff` are "iff" versions of these
- `AmpleSet.vadd`: in particular, ample-ness is invariant under affine translations
- `AmpleSet.of_one_lt_codim`: a linear subspace of codimension at least two has an ample complement.
  This is the crucial geometric ingredient which allows to apply convex integration
  to the theory of immersions in positive codimension.

## Implementation notes

A priori, the definition of ample subset asks for a vector space structure and a topology on the
ambient type without any link between those structures. In practice, we care most about using these
for finite-dimensional vector spaces with their natural topology.

All vector spaces in the file are real vector spaces. While the definition generalises to other
connected fields, that is not useful in practice.

## Tags
ample set
-/

/-! ## Definition and invariance -/

open Set

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

def AmpleSet (s : Set F) : Prop :=
  ∀ x ∈ s, convexHull ℝ (connectedComponentIn s x) = univ
