/-
Extracted from Order/SuccPred/Tree.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Rooted trees

This file proves basic results about rooted trees, represented using the ancestorship order.
This is a `PartialOrder`, with `PredOrder` with the immediate parent as a predecessor, and an
`OrderBot` which is the root. We also have an `IsPredArchimedean` assumption to prevent infinite
dangling chains.
-/

variable {α : Type*} [PartialOrder α] [PredOrder α] [IsPredArchimedean α]

namespace IsPredArchimedean

variable [OrderBot α]

section DecidableEq

variable [DecidableEq α]

def findAtom (r : α) : α :=
  Order.pred^[Nat.find (bot_le (a := r)).exists_pred_iterate - 1] r
