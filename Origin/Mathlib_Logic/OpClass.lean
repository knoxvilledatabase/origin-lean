/-
Extracted from Logic/OpClass.lean
Genuine: 4 of 9 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Typeclasses for commuting heterogeneous operations

The three classes in this file are for two-argument functions where one input is of type `α`,
the output is of type `β` and the other input is of type `α` or `β`.
They express the property that permuting arguments of type `α` does not change the result.

## Main definitions

* `IsSymmOp`: for `op : α → α → β`, `op a b = op b a`.
* `LeftCommutative`: for `op : α → β → β`, `op a₁ (op a₂ b) = op a₂ (op a₁ b)`.
* `RightCommutative`: for `op : β → α → β`, `op (op b a₁) a₂ = op (op b a₂) a₁`.
-/

universe u v

variable {α : Sort u} {β : Sort v}

class IsSymmOp (op : α → α → β) : Prop where
  /-- A symmetric operation satisfies `op a b = op b a`. -/
  symm_op : ∀ a b, op a b = op b a

class LeftCommutative (op : α → β → β) : Prop where
  /-- A left-commutative operation satisfies `op a₁ (op a₂ b) = op a₂ (op a₁ b)`. -/
  left_comm : (a₁ a₂ : α) → (b : β) → op a₁ (op a₂ b) = op a₂ (op a₁ b)

class RightCommutative (op : β → α → β) : Prop where
  /-- A right-commutative operation satisfies `op (op b a₁) a₂ = op (op b a₂) a₁`. -/
  right_comm : (b : β) → (a₁ a₂ : α) → op (op b a₁) a₂ = op (op b a₂) a₁

-- INSTANCE (free from Core): (priority

theorem IsSymmOp.flip_eq (op : α → α → β) [IsSymmOp op] : flip op = op :=
  funext fun a ↦ funext fun b ↦ (IsSymmOp.symm_op a b).symm

-- INSTANCE (free from Core): {f

-- INSTANCE (free from Core): {f

-- INSTANCE (free from Core): {f

-- INSTANCE (free from Core): {f
