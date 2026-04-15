/-
Extracted from Data/List/Shortlex.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Shortlex ordering of lists.

Given a relation `r` on `α`, the shortlex order on `List α` is defined by `L < M` iff
* `L.length < M.length`
* `L.length = M.length` and `L < M` under the lexicographic ordering over `r` on lists

## Main results

We show that if `r` is well-founded, so too is the shortlex order over `r`

## See also

Related files are:
* `Mathlib/Data/List/Lex.lean`: Lexicographic order on `List α`.
* `Mathlib/Data/DFinsupp/WellFounded.lean`: Well-foundedness of lexicographic orders on `DFinsupp`
  and `Pi`.
-/

/-! ### shortlex ordering -/

namespace List

def Shortlex {α : Type*} (r : α → α → Prop) : List α → List α → Prop :=
  InvImage (Prod.Lex (· < ·) (List.Lex r)) fun a ↦ (a.length, a)

variable {α : Type*} {r : α → α → Prop}

theorem Shortlex.of_length_lt {s t : List α} (h : s.length < t.length) : Shortlex r s t :=
  Prod.Lex.left _ _ h

theorem Shortlex.of_lex {s t : List α} (len_eq : s.length = t.length) (h_lex : List.Lex r s t) :
    Shortlex r s t := by
  apply Prod.lex_def.mpr
  right
  exact ⟨len_eq, h_lex⟩

theorem shortlex_def {s t : List α} :
    Shortlex r s t ↔ s.length < t.length ∨ s.length = t.length ∧ Lex r s t := Prod.lex_def

theorem shortlex_iff_lex {s t : List α} (h : s.length = t.length) :
    Shortlex r s t ↔ List.Lex r s t := by
  simp [shortlex_def, h]

theorem shortlex_cons_iff [Std.Irrefl r] {a : α} {s t : List α} :
    Shortlex r (a :: s) (a :: t) ↔ Shortlex r s t := by
  simp only [shortlex_def, length_cons, add_lt_add_iff_right, add_left_inj, List.lex_cons_iff]

alias ⟨Shortlex.of_cons, Shortlex.cons⟩ := shortlex_cons_iff
