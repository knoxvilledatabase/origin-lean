/-
Extracted from Algebra/Group/AddChar.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Characters from additive to multiplicative monoids

Let `A` be an additive monoid, and `M` a multiplicative one. An *additive character* of `A` with
values in `M` is simply a map `A → M` which intertwines the addition operation on `A` with the
multiplicative operation on `M`.

We define these objects, using the namespace `AddChar`, and show that if `A` is a commutative group
under addition, then the additive characters are also a group (written multiplicatively). Note that
we do not need `M` to be a group here.

We also include some constructions specific to the case when `A = R` is a ring; then we define
`mulShift ψ r`, where `ψ : AddChar R M` and `r : R`, to be the character defined by
`x ↦ ψ (r * x)`.

For more refined results of a number-theoretic nature (primitive characters, Gauss sums, etc)
see `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean`.

## Implementation notes

Due to their role as the dual of an additive group, additive characters must themselves be an
additive group. This contrasts to their pointwise operations which make them a multiplicative group.
We simply define both the additive and multiplicative group structures and prove them equal.

For more information on this design decision, see the following zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Additive.20characters

## Tags

additive character
-/

/-!
### Definitions related to and results on additive characters
-/

open Function Multiplicative

open Finset hiding card

open Fintype (card)

section AddCharDef

variable (A : Type*) [AddMonoid A]

variable (M : Type*) [Monoid M]

structure AddChar where
  /-- The underlying function.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : A → M
  /-- The function maps `0` to `1`.

  Do not use this directly. Instead use `AddChar.map_zero_eq_one`. -/
  map_zero_eq_one' : toFun 0 = 1
  /-- The function maps addition in `A` to multiplication in `M`.

  Do not use this directly. Instead use `AddChar.map_add_eq_mul`. -/
  map_add_eq_mul' : ∀ a b : A, toFun (a + b) = toFun a * toFun b

end AddCharDef

namespace AddChar

section Basic

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

-- INSTANCE (free from Core): instFunLike

initialize_simps_projections AddChar (toFun → apply) -- needs to come after FunLike instance
