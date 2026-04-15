/-
Extracted from Algebra/Order/AbsoluteValue/Basic.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Absolute values

This file defines a bundled type of absolute values `AbsoluteValue R S`.

## Main definitions

* `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`.
* `AbsoluteValue.abs` is the "standard" absolute value on `S`, mapping negative `x` to `-x`.
* `AbsoluteValue.toMonoidWithZeroHom`: absolute values mapping to a
  linear ordered field preserve `0`, `*` and `1`
* `IsAbsoluteValue`: a type class stating that `f : β → α` satisfies the axioms of an absolute
  value
-/

variable {ι α R S : Type*}

structure AbsoluteValue (R S : Type*) [Semiring R] [Semiring S] [PartialOrder S]
    extends R →ₙ* S where
  /-- The absolute value is nonnegative -/
  nonneg' : ∀ x, 0 ≤ toFun x
  /-- The absolute value is positive definitive -/
  eq_zero' : ∀ x, toFun x = 0 ↔ x = 0
  /-- The absolute value satisfies the triangle inequality -/
  add_le' : ∀ x y, toFun (x + y) ≤ toFun x + toFun y

namespace AbsoluteValue

attribute [nolint docBlame] AbsoluteValue.toMulHom

section OrderedSemiring

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

-- INSTANCE (free from Core): funLike

-- INSTANCE (free from Core): zeroHomClass

-- INSTANCE (free from Core): mulHomClass

-- INSTANCE (free from Core): nonnegHomClass

-- INSTANCE (free from Core): subadditiveHomClass
