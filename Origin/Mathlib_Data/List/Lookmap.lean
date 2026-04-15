/-
Extracted from Data/List/Lookmap.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! ### lookmap -/

variable {α β : Type*}

namespace List

variable (f : α → Option α)

private theorem lookmap.go_append (l : List α) (acc : Array α) :
    lookmap.go f l acc = acc.toListAppend (lookmap f l) := by
  cases l with
  | nil => simp [go, lookmap]
  | cons hd tl =>
    rw [lookmap, go, go]
    cases f hd with
    | none =>
      simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.toList_push]
      rfl
    | some a => rfl
