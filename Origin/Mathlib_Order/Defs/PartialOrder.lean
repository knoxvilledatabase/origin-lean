/-
Extracted from Order/Defs/PartialOrder.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Orders

Defines classes for preorders and partial orders
and proves some basic lemmas about them.

We also define covering relations on a preorder.
We say that `b` *covers* `a` if `a < b` and there is no element in between.
We say that `b` *weakly covers* `a` if `a ≤ b` and there is no element between `a` and `b`.
In a partial order this is equivalent to `a ⋖ b ∨ a = b`,
in a preorder this is equivalent to `a ⋖ b ∨ (a ≤ b ∧ b ≤ a)`

## Notation

* `a ⋖ b` means that `b` covers `a`.
* `a ⩿ b` means that `b` weakly covers `a`.
-/

variable {α : Type*}

section Preorder

/-!
### Definition of `Preorder` and lemmas about types with a `Preorder`
-/

class Preorder (α : Type*) extends LE α, LT α where
  protected le_refl : ∀ a : α, a ≤ a
  protected le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  protected lt_iff_le_not_ge : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

attribute [to_dual self (reorder := le_trans (a c, 4 5), lt_iff_le_not_ge (a b))] Preorder.mk

-- INSTANCE (free from Core): [Preorder

-- INSTANCE (free from Core): [Preorder

variable [Preorder α] {a b c : α}
