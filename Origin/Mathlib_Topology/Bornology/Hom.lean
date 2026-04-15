/-
Extracted from Topology/Bornology/Hom.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Locally bounded maps

This file defines locally bounded maps between bornologies.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `LocallyBoundedMap`: Locally bounded maps. Maps which preserve boundedness.

## Typeclasses

* `LocallyBoundedMapClass`
-/

open Bornology Filter Function Set

variable {F α β γ δ : Type*}

structure LocallyBoundedMap (α β : Type*) [Bornology α] [Bornology β] where
  /-- The function underlying a locally bounded map -/
  toFun : α → β
  /-- The pullback of the `Bornology.cobounded` filter under the function is contained in the
  cobounded filter. Equivalently, the function maps bounded sets to bounded sets. -/
  comap_cobounded_le' : (cobounded β).comap toFun ≤ cobounded α

class LocallyBoundedMapClass (F : Type*) (α β : outParam Type*) [Bornology α]
    [Bornology β] [FunLike F α β] : Prop where
  /-- The pullback of the `Bornology.cobounded` filter under the function is contained in the
  cobounded filter. Equivalently, the function maps bounded sets to bounded sets. -/
  comap_cobounded_le (f : F) : (cobounded β).comap f ≤ cobounded α

end

export LocallyBoundedMapClass (comap_cobounded_le)

variable [FunLike F α β]

theorem Bornology.IsBounded.image [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] (f : F)
    {s : Set α} (hs : IsBounded s) : IsBounded (f '' s) :=
  comap_cobounded_le_iff.1 (comap_cobounded_le f) hs
