/-
Extracted from Data/List/Chain.lean
Genuine: 14 of 14 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relation chain

This file provides basic results about `List.IsChain` from Batteries.
A list `[a₁, a₂, ..., aₙ]` satisfies `IsChain` with respect to the relation `r` if `r a₁ a₂`
and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `IsChain r [a₁, a₂, ..., aₙ]`.
A graph-specialized version is in development and will hopefully be added under `combinatorics.`
sometime soon.
-/

assert_not_imported Mathlib.Algebra.Order.Group.Nat

universe u v

open Nat

namespace List

variable {α : Type u} {β : Type v} {R r : α → α → Prop} {l l₁ l₂ : List α} {a b : α}

mk_iff_of_inductive_prop List.IsChain List.isChain_iff

theorem isChain_nil : IsChain R [] := .nil

theorem isChain_singleton (a : α) : IsChain R [a] := .singleton _

theorem isChain_cons_iff (R : α → α → Prop) (a : α) (l : List α) :
    IsChain R (a :: l) ↔ l = [] ∨
      ∃ (b : α) (l' : List α), R a b ∧ IsChain R (b :: l') ∧ l = b :: l' :=
  (isChain_iff _ _).trans <| by
    simp only [cons_ne_nil, List.cons_eq_cons, exists_and_right,
      exists_eq', true_and, exists_and_left, false_or]
    grind

theorem IsChain.imp_of_mem_tail_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l.tail → R a b → S a b) (p : IsChain R l) : IsChain S l := by
  induction p with grind

theorem IsChain.imp_of_mem_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l → R a b → S a b) (p : IsChain R l) : IsChain S l :=
  p.imp_of_mem_tail_imp (H · · · <| mem_of_mem_tail ·)

theorem IsChain.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp fun a b => (H a b).1, IsChain.imp fun a b => (H a b).2⟩

theorem IsChain.iff_of_mem_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l → (R a b ↔ S a b)) : IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp_of_mem_imp (Iff.mp <| H · · · ·), IsChain.imp_of_mem_imp (Iff.mpr <| H · · · ·)⟩

theorem IsChain.iff_of_mem_tail_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l.tail → (R a b ↔ S a b)) : IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp_of_mem_tail_imp (Iff.mp <| H · · · ·),
  IsChain.imp_of_mem_tail_imp (Iff.mpr <| H · · · ·)⟩

theorem IsChain.iff_mem {l : List α} :
    IsChain R l ↔ IsChain (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l :=
  IsChain.iff_of_mem_imp <| by grind

theorem IsChain.iff_mem_mem_tail {l : List α} :
    IsChain R l ↔ IsChain (fun x y => x ∈ l ∧ y ∈ l.tail ∧ R x y) l :=
  IsChain.iff_of_mem_tail_imp <| by grind

theorem isChain_pair {x y} : IsChain R [x, y] ↔ R x y := by
  simp only [IsChain.singleton, isChain_cons_cons, and_true]

theorem isChain_isInfix : ∀ l : List α, IsChain (fun x y => [x, y] <:+: l) l
  | [] => .nil
  | [_] => .singleton _
  | a :: b :: l => .cons_cons ⟨[], l, by simp⟩
    ((isChain_isInfix (b :: l)).imp fun _ _ h => h.trans ⟨[a], [], by simp⟩)

theorem isChain_split {c : α} {l₁ l₂ : List α} :
    IsChain R (l₁ ++ c :: l₂) ↔ IsChain R (l₁ ++ [c]) ∧ IsChain R (c :: l₂) := by
  induction l₁ using twoStepInduction generalizing l₂ with grind

theorem isChain_cons_split {c : α} {l₁ l₂ : List α} :
    IsChain R (a :: (l₁ ++ c :: l₂)) ↔ IsChain R (a :: (l₁ ++ [c])) ∧ IsChain R (c :: l₂) := by
  simp_rw [← cons_append, isChain_split (l₂ := l₂)]
