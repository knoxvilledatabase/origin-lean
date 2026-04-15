/-
Extracted from Order/Hom/BoundedLattice.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bounded lattice homomorphisms

This file defines bounded lattice homomorphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `SupBotHom`: Finitary supremum homomorphisms. Maps which preserve `⊔` and `⊥`.
* `InfTopHom`: Finitary infimum homomorphisms. Maps which preserve `⊓` and `⊤`.
* `BoundedLatticeHom`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `SupBotHomClass`
* `InfTopHomClass`
* `BoundedLatticeHomClass`

## TODO

Do we need more intersections between `BotHom`, `TopHom` and lattice homomorphisms?
-/

open Function

variable {F α β γ δ : Type*}

structure SupBotHom (α β : Type*) [Max α] [Max β] [Bot α] [Bot β]
  extends SupHom α β, BotHom α β where
