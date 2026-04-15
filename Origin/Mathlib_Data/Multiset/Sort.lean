/-
Extracted from Data/Multiset/Sort.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

public meta import Mathlib.Data.Multiset.Defs

/-!
# Construct a sorted list from a multiset.
-/

variable {α β : Type*}

namespace Multiset

open List

section sort

def sort (s : Multiset α) (r : α → α → Prop := by exact fun a b => a ≤ b)
    [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] : List α :=
  Quot.liftOn s (mergeSort · (r · ·)) fun _ _ h =>
    ((mergeSort_perm _ _).trans <| h.trans (mergeSort_perm _ _).symm).eq_of_pairwise' (r := r)
      (pairwise_mergeSort' _ _) (pairwise_mergeSort' _ _)

variable (a : α) (f : α → β) (l : List α) (s : Multiset α)

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

variable (r' : β → β → Prop) [DecidableRel r'] [IsTrans β r'] [Std.Antisymm r'] [Std.Total r']
