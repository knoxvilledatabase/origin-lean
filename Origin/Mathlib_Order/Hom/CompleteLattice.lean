/-
Extracted from Order/Hom/CompleteLattice.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Complete lattice homomorphisms

This file defines frame homomorphisms and complete lattice homomorphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `sSupHom`: Maps which preserve `⨆`.
* `sInfHom`: Maps which preserve `⨅`.
* `FrameHom`: Frame homomorphisms. Maps which preserve `⨆`, `⊓` and `⊤`.
* `CompleteLatticeHom`: Complete lattice homomorphisms. Maps which preserve `⨆` and `⨅`.

## Typeclasses

* `sSupHomClass`
* `sInfHomClass`
* `FrameHomClass`
* `CompleteLatticeHomClass`

## Concrete homs

* `CompleteLatticeHom.setPreimage`: `Set.preimage` as a complete lattice homomorphism.

## TODO

Frame homs are Heyting homs.
-/

assert_not_exists Monoid

open Function OrderDual Set

variable {F α β γ δ : Type*} {ι : Sort*} {κ : ι → Sort*}

structure sSupHom (α β : Type*) [SupSet α] [SupSet β] where
  /-- The underlying function of a sSupHom. -/
  toFun : α → β
  /-- The proposition that a `sSupHom` commutes with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)
