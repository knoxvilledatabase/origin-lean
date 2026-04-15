/-
Extracted from Algebra/Ring/Hom/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homomorphisms of semirings and rings

This file defines bundled homomorphisms of (non-unital) semirings and rings. As with monoid and
groups, we use the same structure `RingHom a β`, a.k.a. `α →+* β`, for both types of homomorphisms.

## Main definitions

* `NonUnitalRingHom`: Non-unital (semi)ring homomorphisms. Additive monoid homomorphism which
  preserve multiplication.
* `RingHom`: (Semi)ring homomorphisms. Monoid homomorphisms which are also additive monoid
  homomorphism.

## Notation

* `→ₙ+*`: Non-unital (semi)ring homs
* `→+*`: (Semi)ring homs

## Implementation notes

* There's a coercion from bundled homs to fun, and the canonical notation is to
  use the bundled hom as a function via this coercion.

* There is no `SemiringHom` -- the idea is that `RingHom` is used.
  The constructor for a `RingHom` between semirings needs a proof of `map_zero`,
  `map_one` and `map_add` as well as `map_mul`; a separate constructor
  `RingHom.mk'` will construct ring homs between rings from monoid homs given
  only a proof that addition is preserved.

## Tags

`RingHom`, `SemiringHom`
-/

assert_not_exists Function.Injective.mulZeroClass semigroupDvd Units.map

open Function

variable {F α β γ : Type*}

structure NonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] extends α →ₙ* β, α →+ β

infixr:25 " →ₙ+* " => NonUnitalRingHom

add_decl_doc NonUnitalRingHom.toMulHom

add_decl_doc NonUnitalRingHom.toAddMonoidHom

section NonUnitalRingHomClass

class NonUnitalRingHomClass (F : Type*) (α β : outParam Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] [FunLike F α β] : Prop
  extends MulHomClass F α β, AddMonoidHomClass F α β

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [FunLike F α β]

variable [NonUnitalRingHomClass F α β]
