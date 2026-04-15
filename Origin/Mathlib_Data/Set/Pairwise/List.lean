/-
Extracted from Data/Set/Pairwise/List.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Translating pairwise relations on sets to lists

On a list with no duplicates, the condition of `Set.Pairwise` and `List.Pairwise` are equivalent.
-/

variable {α : Type*} {r : α → α → Prop}

namespace List

variable {l : List α}

theorem Nodup.pairwise_of_set_pairwise {l : List α} {r : α → α → Prop} (hl : l.Nodup)
    (h : {x | x ∈ l}.Pairwise r) : l.Pairwise r :=
  hl.pairwise_of_forall_ne h
