/-
Extracted from SetTheory/Ordinal/CantorNormalForm.lean
Genuine: 8 of 16 | Dissolved: 8 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`Ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

# Implementation notes

We implement `Ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

# Todo

- Add API for the coefficients of the Cantor normal form.
- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/

noncomputable section

universe u

open List

namespace Ordinal

-- DISSOLVED: CNFRec

termination_by o

decreasing_by exact mod_opow_log_lt_self b h

-- DISSOLVED: CNFRec_zero

-- DISSOLVED: CNFRec_pos

@[pp_nodot]
def CNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  CNFRec b [] (fun o _ IH ↦ (log b o, o / b ^ log b o)::IH) o

@[simp]
theorem CNF_zero (b : Ordinal) : CNF b 0 = [] :=
  CNFRec_zero b _ _

-- DISSOLVED: CNF_ne_zero

-- DISSOLVED: zero_CNF

-- DISSOLVED: one_CNF

-- DISSOLVED: CNF_of_le_one

-- DISSOLVED: CNF_of_lt

theorem CNF_foldr (b o : Ordinal) : (CNF b o).foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0 = o := by
  refine CNFRec b ?_ ?_ o
  · rw [CNF_zero, foldr_nil]
  · intro o ho IH
    rw [CNF_ne_zero ho, foldr_cons, IH, div_add_mod]

theorem CNF_fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} :
    x ∈ CNF b o → x.1 ≤ log b o := by
  refine CNFRec b ?_ (fun o ho H ↦ ?_) o
  · simp
  · rw [CNF_ne_zero ho, mem_cons]
    rintro (rfl | h)
    · rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

theorem CNF_fst_le {b o : Ordinal.{u}} {x : Ordinal × Ordinal} (h : x ∈ CNF b o) : x.1 ≤ o :=
  (CNF_fst_le_log h).trans <| log_le_self _ _

theorem CNF_lt_snd {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → 0 < x.2 := by
  refine CNFRec b (by simp) (fun o ho IH ↦ ?_) o
  rw [CNF_ne_zero ho]
  rintro (h | ⟨_, h⟩)
  · exact div_opow_log_pos b ho
  · exact IH h

theorem CNF_snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} :
    x ∈ CNF b o → x.2 < b := by
  refine CNFRec b ?_ (fun o ho IH ↦ ?_) o
  · simp
  · rw [CNF_ne_zero ho]
    intro h
    obtain rfl | h := mem_cons.mp h
    · exact div_opow_log_lt o hb
    · exact IH h

theorem CNF_sorted (b o : Ordinal) : ((CNF b o).map Prod.fst).Sorted (· > ·) := by
  refine CNFRec b ?_ (fun o ho IH ↦ ?_) o
  · rw [CNF_zero]
    exact sorted_nil
  · rcases le_or_lt b 1 with hb | hb
    · rw [CNF_of_le_one hb ho]
      exact sorted_singleton _
    · obtain hob | hbo := lt_or_le o b
      · rw [CNF_of_lt ho hob]
        exact sorted_singleton _
      · rw [CNF_ne_zero ho, map_cons, sorted_cons]
        refine ⟨fun a H ↦ ?_, IH⟩
        rw [mem_map] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (CNF_fst_le_log H).trans_lt (log_mod_opow_log_lt_log_self hb hbo)

end Ordinal
