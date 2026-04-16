/-
Extracted from Data/List/Enum.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Data.List.Basic

noncomputable section

/-!
# Properties of `List.enum`

## Deprecation note

Many lemmas in this file have been replaced by theorems in Lean4,
in terms of `xs[i]?` and `xs[i]` rather than `get` and `get?`.

The deprecated results here are unused in Mathlib.
Any downstream users who can not easily adapt may remove the deprecations as needed.
-/

namespace List

variable {α : Type*}

theorem mk_add_mem_enumFrom_iff_get? {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  simp [mem_iff_get?]

theorem mk_mem_enumFrom_iff_le_and_get?_sub {n i : ℕ} {x : α} {l : List α} :
    (i, x) ∈ enumFrom n l ↔ n ≤ i ∧ l.get? (i - n) = x := by
  simp [mk_mem_enumFrom_iff_le_and_getElem?_sub]

theorem mk_mem_enum_iff_get? {i : ℕ} {x : α} {l : List α} : (i, x) ∈ enum l ↔ l.get? i = x := by
  simp [enum, mk_mem_enumFrom_iff_le_and_getElem?_sub]

set_option linter.deprecated false in
@[deprecated mem_enum_iff_getElem? (since := "2024-08-15")]

theorem mem_enum_iff_get? {x : ℕ × α} {l : List α} : x ∈ enum l ↔ l.get? x.1 = x.2 :=
  mk_mem_enum_iff_get?

theorem forall_mem_enumFrom {l : List α} {n : ℕ} {p : ℕ × α → Prop} :
    (∀ x ∈ l.enumFrom n, p x) ↔ ∀ (i : ℕ) (_ : i < length l), p (n + i, l[i]) := by
  simp only [forall_mem_iff_getElem, getElem_enumFrom, enumFrom_length]

theorem forall_mem_enum {l : List α} {p : ℕ × α → Prop} :
    (∀ x ∈ l.enum, p x) ↔ ∀ (i : ℕ) (_ : i < length l), p (i, l[i]) :=
  forall_mem_enumFrom.trans <| by simp

theorem exists_mem_enumFrom {l : List α} {n : ℕ} {p : ℕ × α → Prop} :
    (∃ x ∈ l.enumFrom n, p x) ↔ ∃ (i : ℕ) (_ : i < length l), p (n + i, l[i]) := by
  simp only [exists_mem_iff_getElem, getElem_enumFrom, enumFrom_length]

theorem exists_mem_enum {l : List α} {p : ℕ × α → Prop} :
    (∃ x ∈ l.enum, p x) ↔ ∃ (i : ℕ) (_ : i < length l), p (i, l[i]) :=
  exists_mem_enumFrom.trans <| by simp

end List
