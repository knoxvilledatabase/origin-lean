/-
Extracted from Algebra/Order/Hom/Monoid.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordered monoid and group homomorphisms

This file defines morphisms between (additive) ordered monoids.

## Types of morphisms

* `OrderAddMonoidHom`: Ordered additive monoid homomorphisms.
* `OrderMonoidHom`: Ordered monoid homomorphisms.
* `OrderAddMonoidIso`: Ordered additive monoid isomorphisms.
* `OrderMonoidIso`: Ordered monoid isomorphisms.

## Notation

* `→+o`: Bundled ordered additive monoid homs. Also use for additive group homs.
* `→*o`: Bundled ordered monoid homs. Also use for group homs.
* `≃+o`: Bundled ordered additive monoid isos. Also use for additive group isos.
* `≃*o`: Bundled ordered monoid isos. Also use for group isos.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical notation is to use the bundled hom as
a function via this coercion.

There is no `OrderGroupHom` -- the idea is that `OrderMonoidHom` is used.
The constructor for `OrderMonoidHom` needs a proof of `map_one` as well as `map_mul`; a separate
constructor `OrderMonoidHom.mk'` will construct ordered group homs (i.e. ordered monoid homs
between ordered groups) given only a proof that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets. This is done when the
instances can be inferred because they are implicit arguments to the type `OrderMonoidHom`. When
they can be inferred from the type it is faster to use this method than to use type class inference.

### Removed typeclasses

This file used to define typeclasses for order-preserving (additive) monoid homomorphisms:
`OrderAddMonoidHomClass`, `OrderMonoidHomClass`, and `OrderMonoidWithZeroHomClass`.

In https://github.com/leanprover-community/mathlib4/pull/10544 we migrated from these typeclasses
to assumptions like `[FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N]`,
making some definitions and lemmas irrelevant.

## Tags

ordered monoid, ordered group
-/

assert_not_exists MonoidWithZero

open Function

variable {F α β γ δ : Type*}

section AddMonoid

structure OrderAddMonoidHom (α β : Type*) [Preorder α] [Preorder β] [AddZeroClass α]
  [AddZeroClass β] extends α →+ β where
  /-- An `OrderAddMonoidHom` is a monotone function. -/
  monotone' : Monotone toFun

infixr:25 " →+o " => OrderAddMonoidHom

structure OrderAddMonoidIso (α β : Type*) [Preorder α] [Preorder β] [Add α] [Add β]
  extends α ≃+ β where
  /-- An `OrderAddMonoidIso` respects `≤`. -/
  map_le_map_iff' {a b : α} : toFun a ≤ toFun b ↔ a ≤ b

infixr:25 " ≃+o " => OrderAddMonoidIso

end AddMonoid

section Monoid
