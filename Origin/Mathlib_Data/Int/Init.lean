/-
Extracted from Data/Int/Init.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic operations on the integers

This file contains some basic lemmas about integers.

See note [foundational algebra order theory].

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries easily.
-/

open Nat

namespace Int

variable {a b c d m n : ℤ}

protected theorem neg_eq_neg {a b : ℤ} (h : -a = -b) : a = b := Int.neg_inj.1 h

/-! ### succ and pred -/

def succ (a : ℤ) := a + 1

def pred (a : ℤ) := a - 1

lemma pred_succ (a : ℤ) : pred (succ a) = a := Int.add_sub_cancel _ _

lemma succ_pred (a : ℤ) : succ (pred a) = a := Int.sub_add_cancel _ _

lemma neg_succ (a : ℤ) : -succ a = pred (-a) := Int.neg_add

lemma succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]

lemma neg_pred (a : ℤ) : -pred a = succ (-a) := by
  rw [← Int.neg_eq_comm.mp (neg_succ (-a)), Int.neg_neg]

lemma pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]

lemma pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n := pred_succ n

lemma neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) := neg_succ n

lemma succ_neg_natCast_succ (n : ℕ) : succ (-Nat.succ n) = -n := succ_neg_succ n
