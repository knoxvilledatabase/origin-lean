/-
Extracted from Topology/ContinuousMap/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous bundled maps

In this file we define the type `ContinuousMap` of continuous bundled maps.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass
which is meant to be satisfied by itself and all stricter types.
-/

open Function

open scoped Topology

structure ContinuousMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  /-- The function `X → Y` -/
  protected toFun : X → Y
  /-- Proposition that `toFun` is continuous -/
  protected continuous_toFun : Continuous toFun := by fun_prop

notation "C(" X ", " Y ")" => ContinuousMap X Y

class ContinuousMapClass (F : Type*) (X Y : outParam Type*)
    [TopologicalSpace X] [TopologicalSpace Y] [FunLike F X Y] : Prop where
  /-- Continuity -/
  map_continuous (f : F) : Continuous f

end

export ContinuousMapClass (map_continuous)

attribute [continuity, fun_prop] map_continuous

section ContinuousMapClass

variable {F X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [FunLike F X Y]

variable [ContinuousMapClass F X Y]
