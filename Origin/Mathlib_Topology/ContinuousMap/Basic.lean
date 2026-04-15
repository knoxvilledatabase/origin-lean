/-
Extracted from Topology/ContinuousMap/Basic.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Continuous bundled maps

In this file we define the type `ContinuousMap` of continuous bundled maps.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/

open Function Topology

section ContinuousMapClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β]

variable [ContinuousMapClass F α β]

theorem map_continuousAt (f : F) (a : α) : ContinuousAt f a :=
  (map_continuous f).continuousAt

theorem map_continuousWithinAt (f : F) (s : Set α) (a : α) : ContinuousWithinAt f s a :=
  (map_continuous f).continuousWithinAt

end ContinuousMapClass

/-! ### Continuous maps -/

namespace ContinuousMap

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

variable {f g : C(α, β)}

protected theorem continuousAt (f : C(α, β)) (x : α) : ContinuousAt f x :=
  map_continuousAt f x

section DiscreteTopology

variable [DiscreteTopology α]
