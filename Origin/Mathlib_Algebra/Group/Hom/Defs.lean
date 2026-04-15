/-
Extracted from Algebra/Group/Hom/Defs.lean
Genuine: 4 of 6 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monoid and group homomorphisms

This file defines the bundled structures for monoid and group homomorphisms. Namely, we define
`MonoidHom` (resp., `AddMonoidHom`) to be bundled homomorphisms between multiplicative (resp.,
additive) monoids or groups.

We also define coercion to a function, and usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

This file also defines the lesser-used (and notation-less) homomorphism types which are used as
building blocks for other homomorphisms:

* `ZeroHom`
* `OneHom`
* `AddHom`
* `MulHom`

## Notation

* `→+`: Bundled `AddMonoid` homs. Also use for `AddGroup` homs.
* `→*`: Bundled `Monoid` homs. Also use for `Group` homs.
* `→ₙ+`: Bundled `AddSemigroup` homs.
* `→ₙ*`: Bundled `Semigroup` homs.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `GroupHom` -- the idea is that `MonoidHom` is used.
The constructor for `MonoidHom` needs a proof of `map_one` as well
as `map_mul`; a separate constructor `MonoidHom.mk'` will construct
group homs (i.e. monoid homs between groups) given only a proof
that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `MonoidHom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

Historically this file also included definitions of unbundled homomorphism classes; they were
deprecated and moved to `Deprecated/Group`.

## Tags

MonoidHom, AddMonoidHom

-/

open Function

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

section Zero

-- DISSOLVED: ZeroHom

-- DISSOLVED: ZeroHomClass

end Zero

section Add

structure AddHom (M : Type*) (N : Type*) [Add M] [Add N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves addition -/
  protected map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

infixr:25 " →ₙ+ " => AddHom

class AddHomClass (F : Type*) (M N : outParam Type*) [Add M] [Add N] [FunLike F M N] : Prop where
  /-- The proposition that the function preserves addition -/
  map_add : ∀ (f : F) (x y : M), f (x + y) = f x + f y

end Add

section add_zero

structure AddMonoidHom (M : Type*) (N : Type*) [AddZero M] [AddZero N]
  extends ZeroHom M N, AddHom M N

attribute [nolint docBlame] AddMonoidHom.toAddHom

attribute [nolint docBlame] AddMonoidHom.toZeroHom

infixr:25 " →+ " => AddMonoidHom

class AddMonoidHomClass (F : Type*) (M N : outParam Type*)
    [AddZero M] [AddZero N] [FunLike F M N] : Prop
    extends AddHomClass F M N, ZeroHomClass F M N

end add_zero

section One

variable [One M] [One N]
