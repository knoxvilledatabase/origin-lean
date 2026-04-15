/-
Extracted from Algebra/Order/Hom/Ring.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered (semi)rings that respect the ordering.

## Main definitions

* `OrderRingHom` : Monotone semiring homomorphisms.
* `OrderRingIso` : Monotone semiring isomorphisms.

## Notation

* `→+*o`: Ordered ring homomorphisms.
* `≃+*o`: Ordered ring isomorphisms.

## Implementation notes

This file used to define typeclasses for order-preserving ring homomorphisms and isomorphisms.
In https://github.com/leanprover-community/mathlib4/pull/10544, we migrated from assumptions like `[FunLike F R S] [OrderRingHomClass F R S]`
to assumptions like `[FunLike F R S] [OrderHomClass F R S] [RingHomClass F R S]`,
making some typeclasses and instances irrelevant.

## Tags

ordered ring homomorphism, order homomorphism
-/

assert_not_exists FloorRing Archimedean

open Function

variable {F α β γ δ : Type*}

structure OrderRingHom (α β : Type*) [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
  [Preorder β] extends α →+* β where
  /-- The proposition that the function preserves the order. -/
  monotone' : Monotone toFun

add_decl_doc OrderRingHom.toRingHom
