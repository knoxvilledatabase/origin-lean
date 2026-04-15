/-
Extracted from Analysis/Convex/Body.lean
Genuine: 5 of 7 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Convex bodies

This file contains the definition of the type `ConvexBody V`
consisting of
convex, compact, nonempty subsets of a real topological vector space `V`.

`ConvexBody V` is a module over the nonnegative reals (`NNReal`) and a pseudo-metric space.
If `V` is a normed space, `ConvexBody V` is a metric space.

## TODO

- define positive convex bodies, requiring the interior to be nonempty
- introduce support sets
- Characterise the interaction of the distance with algebraic operations, e.g.
  `dist (a • K) (a • L) = ‖a‖ * dist K L`, `dist (a +ᵥ K) (a +ᵥ L) = dist K L`

## Tags

convex, convex body
-/

open scoped Pointwise Topology NNReal

variable {V : Type*}

structure ConvexBody (V : Type*) [TopologicalSpace V] [AddCommMonoid V] [SMul ℝ V] where
  /-- The **carrier set** underlying a convex body: the set of points contained in it -/
  carrier : Set V
  /-- A convex body has convex carrier set -/
  convex' : Convex ℝ carrier
  /-- A convex body has compact carrier set -/
  isCompact' : IsCompact carrier
  /-- A convex body has non-empty carrier set -/
  nonempty' : carrier.Nonempty

namespace ConvexBody

section TVS

variable [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

protected theorem convex (K : ConvexBody V) : Convex ℝ (K : Set V) :=
  K.convex'

protected theorem isCompact (K : ConvexBody V) : IsCompact (K : Set V) :=
  K.isCompact'

protected theorem isClosed [T2Space V] (K : ConvexBody V) : IsClosed (K : Set V) :=
  K.isCompact.isClosed

protected theorem nonempty (K : ConvexBody V) : (K : Set V).Nonempty :=
  K.nonempty'
