/-
Extracted from Topology/VectorBundle/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Vector bundles

In this file we define (topological) vector bundles.

Let `B` be the base space, let `F` be a normed space over a normed field `R`, and let
`E : B → Type*` be a `FiberBundle` with fiber `F`, in which, for each `x`, the fiber `E x` is a
topological vector space over `R`.

To have a vector bundle structure on `Bundle.TotalSpace F E`, one should additionally have the
following properties:

* The bundle trivializations in the trivialization atlas should be continuous linear equivs in the
  fibers;
* For any two trivializations `e`, `e'` in the atlas the transition function considered as a map
  from `B` into `F →L[R] F` is continuous on `e.baseSet ∩ e'.baseSet` with respect to the operator
  norm topology on `F →L[R] F`.

If these conditions are satisfied, we register the typeclass `VectorBundle R F E`.

We define constructions on vector bundles like pullbacks and direct sums in other files.

## Main Definitions

* `Bundle.Trivialization.IsLinear`: a class stating that a trivialization is fiberwise linear
  on its base set.
* `Bundle.Trivialization.linearEquivAt` and `Bundle.Trivialization.continuousLinearMapAt` are the
  (continuous) linear fiberwise equivalences a trivialization induces.
* They have forward maps `Bundle.Trivialization.linearMapAt` /
  `Bundle.Trivialization.continuousLinearMapAt` and inverses `Bundle.Trivialization.symmₗ` /
  `Bundle.Trivialization.symmL`. Note that these are all defined
  everywhere, since they are extended using the zero function.
* `Bundle.Trivialization.coordChangeL` is the coordinate change induced by two trivializations.
  It only makes sense on the intersection of their base sets,
  but is extended outside it using the identity.
* Given a continuous (semi)linear map between `E x` and `E' y` where `E` and `E'` are bundles over
  possibly different base sets, `ContinuousLinearMap.inCoordinates` turns this into a continuous
  (semi)linear map between the chosen fibers of those bundles.

## Implementation notes

The implementation choices in the vector bundle definition are discussed in the "Implementation
notes" section of `Mathlib/Topology/FiberBundle/Basic.lean`.

## Tags
Vector bundle
-/

noncomputable section

open Bundle Set Topology

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)

section TopologicalVectorSpace

variable {F E}

variable [Semiring R] [TopologicalSpace F] [TopologicalSpace B]

protected class Bundle.Pretrivialization.IsLinear [AddCommMonoid F] [Module R F]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)] (e : Pretrivialization F (π F E)) : Prop where
  linear : ∀ b ∈ e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2

namespace Bundle.Pretrivialization

variable (e : Pretrivialization F (π F E)) {x : TotalSpace F E} {b : B} {y : E b}

theorem linear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
    [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet) :
    IsLinearMap R fun x : E b => (e ⟨b, x⟩).2 :=
  IsLinear.linear b hb

variable [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
