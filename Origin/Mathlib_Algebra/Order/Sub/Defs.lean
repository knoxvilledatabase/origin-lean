/-
Extracted from Algebra/Order/Sub/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordered Subtraction

This file proves lemmas relating (truncated) subtraction with an order. We provide a class
`OrderedSub` stating that `a - b ≤ c ↔ a ≤ c + b`.

The subtraction discussed here could both be normal subtraction in an additive group or truncated
subtraction on a canonically ordered monoid (`ℕ`, `Multiset`, `ENNReal`, ...)

## Implementation details

`OrderedSub` is a mixin type-class, so that we can use the results in this file even in cases
where we don't have a `CanonicallyOrderedAdd` instance
(even though that is our main focus). Conversely, this means we can use
`CanonicallyOrderedAdd` without necessarily having to define a subtraction.

The results in this file are ordered by the type-class assumption needed to prove it.
This means that similar results might not be close to each other. Furthermore, we don't prove
implications if a bi-implication can be proven under the same assumptions.

Lemmas using this class are named using `tsub` instead of `sub` (short for "truncated subtraction").
This is to avoid naming conflicts with similar lemmas about ordered groups.

We provide a second version of most results that require `[AddLeftReflectLE α]`. In the
second version we replace this type-class assumption by explicit `AddLECancellable` assumptions.

TODO: maybe we should make a multiplicative version of this, so that we can replace some identical
lemmas about subtraction/division in `Ordered[Add]CommGroup` with these.

TODO: generalize `Nat.le_of_le_of_sub_le_sub_right`, `Nat.sub_le_sub_right_iff`,
  `Nat.mul_self_sub_mul_self_eq`
-/

variable {α : Type*}

class OrderedSub (α : Type*) [LE α] [Add α] [Sub α] : Prop where
  /-- `a - b` provides a lower bound on `c` such that `a ≤ c + b`. -/
  tsub_le_iff_right : ∀ a b c : α, a - b ≤ c ↔ a ≤ c + b

section Add
