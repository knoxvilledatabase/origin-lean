/-
Extracted from Data/Finset/Sort.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Construct a sorted list from a finset.
-/

namespace Finset

open Multiset Nat

variable {α β : Type*}

/-! ### sort -/

section sort

def sort (s : Finset α) (r : α → α → Prop := by exact fun a b => a ≤ b)
    [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] : List α :=
  Multiset.sort s.1 r

variable (f : α ↪ β) (s : Finset α)

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

variable (r' : β → β → Prop) [DecidableRel r'] [IsTrans β r'] [Std.Antisymm r'] [Std.Total r']
