/-
Extracted from LinearAlgebra/RootSystem/RootPairingCat.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of root pairings
This file defines the category of root pairings, following the definition of category of root data
given in SGA III Exp. 21 Section 6.

## Main definitions:
* `RootPairingCat`: Objects are root pairings.

## TODO

* Forgetful functors
* Functions passing between module maps and root pairing homs

## Implementation details

This is mostly copied from `ModuleCat`.

-/

open Set Function CategoryTheory

noncomputable section

universe v u

variable {R : Type u} [CommRing R]

structure RootPairingCat (R : Type u) [CommRing R] where
  /-- The weight space of a root pairing. -/
  weight : Type v
  [weightIsAddCommGroup : AddCommGroup weight]
  [weightIsModule : Module R weight]
  /-- The coweight space of a root pairing. -/
  coweight : Type v
  [coweightIsAddCommGroup : AddCommGroup coweight]
  [coweightIsModule : Module R coweight]
  /-- The set that indexes roots and coroots. -/
  index : Type v
  /-- The root pairing structure. -/
  pairing : RootPairing index R weight coweight

attribute [instance] RootPairingCat.weightIsAddCommGroup RootPairingCat.weightIsModule

attribute [instance] RootPairingCat.coweightIsAddCommGroup RootPairingCat.coweightIsModule

namespace RootPairingCat

-- INSTANCE (free from Core): category

end RootPairingCat
