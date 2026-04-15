/-
Extracted from Topology/Hom/Open.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous open maps

This file defines bundled continuous open maps.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `ContinuousOpenMap`: Continuous open maps.

## Typeclasses

* `ContinuousOpenMapClass`
-/

open Function

variable {F α β γ δ : Type*}

structure ContinuousOpenMap (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMap α β where
  map_open' : IsOpenMap toFun
