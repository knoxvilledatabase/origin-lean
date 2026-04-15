/-
Extracted from Data/List/TakeWhile.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! ### List.takeWhile and List.dropWhile -/

namespace List

variable {α : Type*} (p : α → Bool)

theorem dropWhile_get_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) :
    ¬p ((l.dropWhile p).get ⟨0, hl⟩) := by
  induction l with
  | nil => cases hl
  | cons hd tl IH =>
    simp only [dropWhile]
    by_cases hp : p hd
    · simp_all only [get_eq_getElem]
      apply IH
      simp_all only [dropWhile_cons_of_pos]
    · simp [hp]

theorem length_dropWhile_le (l : List α) : (dropWhile p l).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [dropWhile, length_cons]
    split
    · lia
    · simp

variable {p} {l : List α}
