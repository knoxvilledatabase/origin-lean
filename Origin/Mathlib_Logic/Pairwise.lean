/-
Extracted from Logic/Pairwise.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relations holding pairwise

This file defines pairwise relations.

## Main declarations

* `Pairwise`: `Pairwise r` states that `r i j` for all `i ≠ j`.
* `Set.Pairwise`: `s.Pairwise r` states that `r i j` for all `i ≠ j` with `i, j ∈ s`.
-/

open Function

variable {α β ι : Type*} {r p : α → α → Prop}

section Pairwise

variable {f : ι → α} {s : Set α} {a b : α}

def Pairwise (r : α → α → Prop) :=
  ∀ ⦃i j⦄, i ≠ j → r i j

theorem Pairwise.mono (hr : Pairwise r) (h : ∀ ⦃i j⦄, r i j → p i j) : Pairwise p :=
  fun _i _j hij => h <| hr hij

protected theorem Pairwise.eq (h : Pairwise r) : ¬r a b → a = b :=
  not_imp_comm.1 <| @h _ _
