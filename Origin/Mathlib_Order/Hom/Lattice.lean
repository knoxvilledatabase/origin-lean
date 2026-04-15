/-
Extracted from Order/Hom/Lattice.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Unbounded lattice homomorphisms

This file defines unbounded lattice homomorphisms. _Bounded_ lattice homomorphisms are defined in
`Mathlib/Order/Hom/BoundedLattice.lean`.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `SupHom`: Maps which preserve `⊔`.
* `InfHom`: Maps which preserve `⊓`.
* `LatticeHom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.

## Typeclasses

* `SupHomClass`
* `InfHomClass`
* `LatticeHomClass`
-/

open Function

variable {F α β γ δ : Type*}

structure SupHom (α β : Type*) [Max α] [Max β] where
  /-- The underlying function of a `SupHom`.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α → β
  /-- A `SupHom` preserves suprema.

  Do not use this directly. Use `map_sup` instead. -/
  map_sup' (a b : α) : toFun (a ⊔ b) = toFun a ⊔ toFun b
