/-
Extracted from Topology/FiberBundle/Trivialization.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Trivializations

## Main definitions

### Basic definitions

* `Bundle.Trivialization F p` : structure extending open partial homeomorphisms, defining a local
  trivialization of a topological space `Z` with projection `p` and fiber `F`.

* `Bundle.Pretrivialization F proj` : trivialization as a partial equivalence, mainly used when the
  topology on the total space has not yet been defined.

### Operations on bundles

We provide the following operations on `Trivialization`s.

* `Bundle.Trivialization.compHomeomorph`: given a local trivialization `e` of a fiber bundle
  `p : Z → B` and a homeomorphism `h : Z' ≃ₜ Z`, returns a local trivialization of the fiber bundle
  `p ∘ h`.

## Implementation notes

Previously, in mathlib, there was a structure `topological_vector_bundle.trivialization` which
extended another structure `topological_fiber_bundle.trivialization` by a linearity hypothesis. As
of PR https://github.com/leanprover-community/mathlib3/pull/17359, we have changed this to a single
structure `Bundle.Trivialization`, together with a mixin class `Bundle.Trivialization.IsLinear`.

This permits all the *data* of a vector bundle to be held at the level of fiber bundles, so that the
same trivializations can underlie an object's structure as (say) a vector bundle over `ℂ` and as a
vector bundle over `ℝ`, as well as its structure simply as a fiber bundle.

This might be a little surprising, given the general trend of the library to ever-increased
bundling.  But in this case the typical motivation for more bundling does not apply: there is no
algebraic or order structure on the whole type of linear (say) trivializations of a bundle.
Indeed, since trivializations only have meaning on their base sets (taking junk values outside), the
type of linear trivializations is not even particularly well-behaved.
-/

open TopologicalSpace Filter Set Bundle Function

open scoped Topology

variable {B : Type*} (F : Type*) {E : B → Type*}

variable {Z : Type*} [TopologicalSpace B] [TopologicalSpace F] {proj : Z → B}

structure Bundle.Pretrivialization (proj : Z → B) extends PartialEquiv Z (B × F) where
  open_target : IsOpen target
  /-- The domain of the local trivialisation (i.e., a subset of the bundle `Z`'s base):
  outside of it, the pretrivialisation returns a junk value -/
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : ∀ p ∈ source, (toFun p).1 = proj p

namespace Bundle.Pretrivialization

variable {F}

variable (e : Pretrivialization F proj) {x : Z}
