/-
Extracted from Data/List/Duplicate.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# List duplicates

## Main definitions

* `List.Duplicate x l : Prop` is an inductive property that holds when `x` is a duplicate in `l`

## Implementation details

In this file, `x ∈+ l` notation is shorthand for `List.Duplicate x l`.

-/

variable {α : Type*}

namespace List

inductive Duplicate (x : α) : List α → Prop
  | cons_mem {l : List α} : x ∈ l → Duplicate x (x :: l)
  | cons_duplicate {y : α} {l : List α} : Duplicate x l → Duplicate x (y :: l)

local infixl:50 " ∈+ " => List.Duplicate

variable {l : List α} {x : α}

theorem Mem.duplicate_cons_self (h : x ∈ l) : x ∈+ x :: l :=
  Duplicate.cons_mem h

theorem Duplicate.duplicate_cons (h : x ∈+ l) (y : α) : x ∈+ y :: l :=
  Duplicate.cons_duplicate h

theorem Duplicate.mem (h : x ∈+ l) : x ∈ l := by
  induction h with
  | cons_mem => exact mem_cons_self
  | cons_duplicate _ hm => exact mem_cons_of_mem _ hm
