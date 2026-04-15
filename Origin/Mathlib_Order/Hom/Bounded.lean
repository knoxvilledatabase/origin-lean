/-
Extracted from Order/Hom/Bounded.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bounded order homomorphisms

This file defines (bounded) order homomorphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `TopHom`: Maps which preserve `⊤`.
* `BotHom`: Maps which preserve `⊥`.
* `BoundedOrderHom`: Bounded order homomorphisms. Monotone maps which preserve `⊤` and `⊥`.

## Typeclasses

* `TopHomClass`
* `BotHomClass`
* `BoundedOrderHomClass`
-/

open Function OrderDual

variable {F α β γ δ : Type*}

structure TopHom (α β : Type*) [Top α] [Top β] where
  /-- The underlying function. The preferred spelling is `DFunLike.coe`. -/
  toFun : α → β
  /-- The function preserves the top element. The preferred spelling is `map_top`. -/
  map_top' : toFun ⊤ = ⊤
