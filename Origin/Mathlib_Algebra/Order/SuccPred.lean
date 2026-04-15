/-
Extracted from Algebra/Order/SuccPred.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Interaction between successors and arithmetic

We define the `SuccAddOrder` and `PredSubOrder` typeclasses, for orders satisfying `succ x = x + 1`
and `pred x = x - 1` respectively. This allows us to transfer the API for successors and
predecessors into these common arithmetical forms.

## Todo

In the future, we will make `x + 1` and `x - 1` the `simp`-normal forms for `succ x` and `pred x`
respectively. This will require a refactor of `Ordinal` first, as the `simp`-normal form is
currently set the other way around.
-/

class SuccAddOrder (α : Type*) [Preorder α] [Add α] [One α] extends SuccOrder α where
  succ_eq_add_one (x : α) : succ x = x + 1

class PredSubOrder (α : Type*) [Preorder α] [Sub α] [One α] extends PredOrder α where
  pred_eq_sub_one (x : α) : pred x = x - 1

variable {α : Type*} {x y : α}

namespace Order

section Preorder

variable [Preorder α]

section Add

variable [Add α] [One α] [SuccAddOrder α]
