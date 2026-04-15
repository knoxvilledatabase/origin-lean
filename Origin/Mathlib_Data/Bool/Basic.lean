/-
Extracted from Data/Bool/Basic.lean
Genuine: 35 of 46 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core

/-!
# Booleans

This file proves various trivial lemmas about Booleans and their
relation to decidable propositions.

## Tags
bool, boolean, Bool, De Morgan

-/

namespace Bool

/-!
This section contains lemmas about Booleans which were present in core Lean 3.
The remainder of this file contains lemmas about Booleans from mathlib 3.
-/

theorem true_eq_false_eq_False : ¬(true = false) := by decide

theorem false_eq_true_eq_False : ¬(false = true) := by decide

theorem eq_false_of_not_eq_true {b : Bool} : ¬b = true → b = false :=
  Eq.mp (eq_false_eq_not_eq_true b)

theorem eq_true_of_not_eq_false {b : Bool} : ¬b = false → b = true :=
  Eq.mp (eq_true_eq_not_eq_false b)

theorem not_eq_true_eq_eq_false (a : Bool) : (not a = true) = (a = false) := by grind

theorem and_eq_false_eq_eq_false_or_eq_false (a b : Bool) :
    ((a && b) = false) = (a = false ∨ b = false) := by grind

theorem or_eq_false_eq_eq_false_and_eq_false (a b : Bool) :
    ((a || b) = false) = (a = false ∧ b = false) := by grind

theorem not_eq_false_eq_eq_true (a : Bool) : (not a = false) = (a = true) := by grind

theorem decide_true {p : Prop} [Decidable p] : p → decide p :=
  (decide_iff p).2

theorem of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (decide_iff p).1

theorem bool_iff_false {b : Bool} : ¬b ↔ b = false := by grind

theorem bool_eq_false {b : Bool} : ¬b → b = false :=
  bool_iff_false.1

theorem decide_false_iff (p : Prop) {_ : Decidable p} : decide p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (decide_iff _))

theorem decide_false {p : Prop} [Decidable p] : ¬p → decide p = false :=
  (decide_false_iff p).2

theorem of_decide_false {p : Prop} [Decidable p] : decide p = false → ¬p :=
  (decide_false_iff p).1

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q :=
  decide_eq_decide.mpr h

theorem coe_xor_iff (a b : Bool) : xor a b ↔ Xor' (a = true) (b = true) := by grind

end

theorem dichotomy (b : Bool) : b = false ∨ b = true := by grind

theorem not_ne_id : not ≠ id := fun h ↦ false_ne_true <| congrFun h true

theorem or_inl {a b : Bool} (H : a) : a || b := by simp [H]

theorem or_inr {a b : Bool} (H : b) : a || b := by grind

theorem and_elim_left : ∀ {a b : Bool}, a && b → a := by decide

theorem and_intro : ∀ {a b : Bool}, a → b → a && b := by decide

theorem and_elim_right : ∀ {a b : Bool}, a && b → b := by decide

lemma eq_not_iff : ∀ {a b : Bool}, a = !b ↔ a ≠ b := by decide

lemma not_eq_iff : ∀ {a b : Bool}, !a = b ↔ a ≠ b := by decide

theorem ne_not {a b : Bool} : a ≠ !b ↔ a = b :=
  not_eq_not

lemma not_ne_self : ∀ b : Bool, (!b) ≠ b := by decide

lemma self_ne_not : ∀ b : Bool, b ≠ !b := by decide

lemma eq_or_eq_not : ∀ a b, a = b ∨ a = !b := by decide

theorem eq_true_of_not_eq_false' {a : Bool} : !a = false → a = true := by grind

theorem eq_false_of_not_eq_true' {a : Bool} : !a = true → a = false := by grind

theorem bne_eq_xor : bne = xor := by constructor

attribute [simp] xor_assoc

theorem xor_iff_ne : ∀ {x y : Bool}, xor x y = true ↔ x ≠ y := by decide

/-! ### De Morgan's laws for Booleans -/

-- INSTANCE (free from Core): linearOrder

theorem lt_iff : ∀ {x y : Bool}, x < y ↔ x = false ∧ y = true := by decide
