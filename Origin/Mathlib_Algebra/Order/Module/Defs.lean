/-
Extracted from Algebra/Order/Module/Defs.lean
Genuine: 12 of 26 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core

/-!
# Monotonicity of scalar multiplication by positive elements

This file defines typeclasses to reason about monotonicity of the operations
* `b ↦ a • b`, "left scalar multiplication"
* `a ↦ a • b`, "right scalar multiplication"

We use eight typeclasses to encode the various properties we care about for those two operations.
These typeclasses are meant to be mostly internal to this file, to set up each lemma in the
appropriate generality.

Less granular typeclasses like `IsOrderedAddMonoid` and `IsOrderedModule` should be enough for most
purposes, and the system is set up so that they imply the correct granular typeclasses here.
If those are enough for you, you may stop reading here! Else, beware that what
follows is a bit technical.


In all that follows, `α` and `β` are orders which have a `0` and such that `α` acts on `β` by scalar
multiplication. Note however that we do not use lawfulness of this action in most of the file. Hence
`•` should be considered here as a mostly arbitrary function `α → β → β`.

We use the following four typeclasses to reason about left scalar multiplication (`b ↦ a • b`):
* `PosSMulMono`: If `a ≥ 0`, then `b₁ ≤ b₂` implies `a • b₁ ≤ a • b₂`.
* `PosSMulStrictMono`: If `a > 0`, then `b₁ < b₂` implies `a • b₁ < a • b₂`.
* `PosSMulReflectLT`: If `a ≥ 0`, then `a • b₁ < a • b₂` implies `b₁ < b₂`.
* `PosSMulReflectLE`: If `a > 0`, then `a • b₁ ≤ a • b₂` implies `b₁ ≤ b₂`.

We use the following four typeclasses to reason about right scalar multiplication (`a ↦ a • b`):
* `SMulPosMono`: If `b ≥ 0`, then `a₁ ≤ a₂` implies `a₁ • b ≤ a₂ • b`.
* `SMulPosStrictMono`: If `b > 0`, then `a₁ < a₂` implies `a₁ • b < a₂ • b`.
* `SMulPosReflectLT`: If `b ≥ 0`, then `a₁ • b < a₂ • b` implies `a₁ < a₂`.
* `SMulPosReflectLE`: If `b > 0`, then `a₁ • b ≤ a₂ • b` implies `a₁ ≤ a₂`.

Furthermore, in a *module*, i.e. a group acted on by a ring, `PosSMulMono` and `SMulPosMono` are
equivalent (they are both the same as `∀ r ≥ 0, ∀ m ≥ 0, 0 ≤ r • m`),
and similarly for `PosSMulStrictMono` and `SMulPosStrictMono`.
To avoid dangerous instances going both, we have the extra two typeclasses:
* `IsOrderedModule`: Conjunction of `PosSMulMono` and `SMulPosMono`
* `IsStrictOrderedModule`: Conjunction of `PosSMulStrictMono` and `SMulPosStrictMono`.

## Constructors

The four typeclasses about nonnegativity can usually be checked only on positive inputs due to their
condition becoming trivial when `a = 0` or `b = 0`. We therefore make the following constructors
available: `PosSMulMono.of_pos`, `PosSMulReflectLT.of_pos`, `SMulPosMono.of_pos`,
`SMulPosReflectLT.of_pos`

## Implications

As `α` and `β` get more and more structure, those typeclasses end up being equivalent. The commonly
used implications are:
* When `α`, `β` are partial orders:
  * `PosSMulStrictMono → PosSMulMono`
  * `SMulPosStrictMono → SMulPosMono`
  * `PosSMulReflectLE → PosSMulReflectLT`
  * `SMulPosReflectLE → SMulPosReflectLT`
* When `β` is a linear order:
  * `PosSMulStrictMono → PosSMulReflectLE`
  * `PosSMulReflectLT → PosSMulMono` (not registered as instance)
  * `SMulPosReflectLT → SMulPosMono` (not registered as instance)
  * `PosSMulReflectLE → PosSMulStrictMono` (not registered as instance)
  * `SMulPosReflectLE → SMulPosStrictMono` (not registered as instance)
* When `α` is a linear order:
  * `SMulPosStrictMono → SMulPosReflectLE`
* When `α` is an ordered ring, `β` an ordered group and also an `α`-module:
  * `PosSMulMono → SMulPosMono`
  * `PosSMulStrictMono → SMulPosStrictMono`
* When `α` is a linear ordered semifield, `β` is an `α`-module:
  * `PosSMulStrictMono → PosSMulReflectLT`
  * `PosSMulMono → PosSMulReflectLE`
* When `α` is a semiring, `β` is an `α`-module with `Module.IsTorsionFree`:
  * `PosSMulMono → PosSMulStrictMono` (not registered as instance)
* When `α` is a ring, `β` is an `α`-module with `Module.IsTorsionFree`:
  * `SMulPosMono → SMulPosStrictMono` (not registered as instance)

Further, the bundled non-granular typeclasses imply the granular ones like so:
* `IsOrderedModule → PosSMulMono`
* `IsOrderedModule → SMulPosMono`
* `IsStrictOrderedModule → PosSMulStrictMono`
* `IsStrictOrderedModule → SMulPosStrictMono`

Unless otherwise stated, all these implications are registered as instances,
which means that in practice you should not worry about these implications.
However, if you encounter a case where you think a statement is true but
not covered by the current implications, please bring it up on Zulip!

## Implementation notes

This file uses custom typeclasses instead of abbreviations of `CovariantClass`/`ContravariantClass`
because:
* They get displayed as classes in the docs. In particular, one can see their list of instances,
  instead of their instances being invariably dumped to the `CovariantClass`/`ContravariantClass`
  list.
* They don't pollute other typeclass searches. Having many abbreviations of the same typeclass for
  different purposes always felt like a performance issue (more instances with the same key, for no
  added benefit), and indeed making the classes here abbreviation previous creates timeouts due to
  the higher number of `CovariantClass`/`ContravariantClass` instances.
* `SMulPosReflectLT`/`SMulPosReflectLE` do not fit in the framework since they relate `≤` on two
  different types. So we would have to generalise `CovariantClass`/`ContravariantClass` to three
  types and two relations.
* Very minor, but the constructors let you work with `a : α`, `h : 0 ≤ a` instead of
  `a : {a : α // 0 ≤ a}`. This actually makes some instances surprisingly cleaner to prove.
* The `CovariantClass`/`ContravariantClass` framework is only useful to automate very simple logic
  anyway. It is easily copied over.

In the future, it would be good to make the corresponding typeclasses in
`Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean` custom typeclasses too.
-/

assert_not_exists Field Finset

open OrderDual

variable (α β : Type*)

section Defs

variable [SMul α β] [Preorder α] [Preorder β]

section Left

variable [Zero α]

class PosSMulMono : Prop where
  /-- Do not use this. Use `smul_le_smul_of_nonneg_left` instead. -/
  protected smul_le_smul_of_nonneg_left ⦃a : α⦄ (ha : 0 ≤ a) ⦃b₁ b₂ : β⦄ (hb : b₁ ≤ b₂) :
    a • b₁ ≤ a • b₂

class PosSMulStrictMono : Prop where
  /-- Do not use this. Use `smul_lt_smul_of_pos_left` instead. -/
  protected smul_lt_smul_of_pos_left ⦃a : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : b₁ < b₂) :
    a • b₁ < a • b₂

class PosSMulReflectLT : Prop where
  /-- Do not use this. Use `lt_of_smul_lt_smul_left` instead. -/
  protected lt_of_smul_lt_smul_left ⦃a : α⦄ (ha : 0 ≤ a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ < a • b₂) :
    b₁ < b₂

class PosSMulReflectLE : Prop where
  /-- Do not use this. Use `le_of_smul_le_smul_left` instead. -/
  protected le_of_smul_le_smul_left ⦃a : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ ≤ a • b₂) :
    b₁ ≤ b₂

end Left

section Right

variable [Zero β]

class SMulPosMono : Prop where
  /-- Do not use this. Use `smul_le_smul_of_nonneg_right` instead. -/
  protected smul_le_smul_of_nonneg_right ⦃b : β⦄ (hb : 0 ≤ b) ⦃a₁ a₂ : α⦄ (ha : a₁ ≤ a₂) :
    a₁ • b ≤ a₂ • b

class SMulPosStrictMono : Prop where
  /-- Do not use this. Use `smul_lt_smul_of_pos_right` instead. -/
  protected smul_lt_smul_of_pos_right ⦃b : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (ha : a₁ < a₂) :
    a₁ • b < a₂ • b

class SMulPosReflectLT : Prop where
  /-- Do not use this. Use `lt_of_smul_lt_smul_right` instead. -/
  protected lt_of_smul_lt_smul_right ⦃b : β⦄ (hb : 0 ≤ b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b < a₂ • b) :
    a₁ < a₂

class SMulPosReflectLE : Prop where
  /-- Do not use this. Use `le_of_smul_le_smul_right` instead. -/
  protected le_of_smul_le_smul_right ⦃b : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b ≤ a₂ • b) :
    a₁ ≤ a₂

end Right

section LeftRight

variable [Zero α] [Zero β]

class IsOrderedModule extends PosSMulMono α β, SMulPosMono α β

class IsStrictOrderedModule extends PosSMulStrictMono α β, SMulPosStrictMono α β

end LeftRight

end Defs

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

section Mul

variable [Zero α] [Mul α] [Preorder α]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end Mul

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): {G

-- INSTANCE (free from Core): {G

section SMul

variable [SMul α β]

section Preorder

variable [Preorder α] [Preorder β]

section Left

variable [Zero α]

lemma monotone_smul_left_of_nonneg [PosSMulMono α β] (ha : 0 ≤ a) : Monotone ((a • ·) : β → β) :=
  PosSMulMono.smul_le_smul_of_nonneg_left ha

lemma strictMono_smul_left_of_pos [PosSMulStrictMono α β] (ha : 0 < a) :
    StrictMono ((a • ·) : β → β) := PosSMulStrictMono.smul_lt_smul_of_pos_left ha
