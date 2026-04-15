/-
Extracted from Data/List/Sort.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sorting algorithms on lists

In this file we define the sorting algorithm `List.insertionSort r` and prove
that we have `(l.insertionSort r l).Pairwise r` under suitable conditions on `r`.

We then define `List.SortedLE`, `List.SortedGE`, `List.SortedLT` and `List.SortedGT`,
predicates which are equivalent to `List.Pairwise` when the relation derives from a
preorder (but which are defined in terms of the monotonicity predicates).
-/

namespace List

section sort

variable {α β : Type*} (r : α → α → Prop) (s : β → β → Prop)

variable [DecidableRel r] [DecidableRel s]

local infixl:50 " ≼ " => r

local infixl:50 " ≼ " => s

/-! ### Insertion sort -/

section InsertionSort

def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≼ b then a :: b :: l else b :: orderedInsert a l
