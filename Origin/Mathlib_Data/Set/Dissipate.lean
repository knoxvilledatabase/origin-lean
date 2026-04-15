/-
Extracted from Data/Set/Dissipate.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Dissipate

The function `dissipate` takes `s : α → Set β` with `LE α` and returns `⋂ y ≤ x, s y`.
It is related to `accumulate s := ⋃ y ≤ x, s y`.

-/

variable {α β : Type*} {s : α → Set β}

namespace Set

def dissipate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋂ y ≤ x, s y

theorem dissipate_eq_biInter_lt {s : ℕ → Set β} {n : ℕ} : dissipate s n = ⋂ k < n + 1, s k := by
  simp_rw [Nat.lt_add_one_iff, dissipate]
