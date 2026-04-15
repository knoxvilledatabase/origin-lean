/-
Extracted from Data/BitVec.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors which can only be stated in Mathlib or downstream
because they refer to other notions defined in Mathlib.

Please do not extend this file further: material about BitVec needed in downstream projects
can either be PR'd to Lean, or kept downstream if it also relies on Mathlib.
-/

namespace BitVec

variable {w : Nat}

open Fin.CommRing in

theorem ofFin_intCast (z : ℤ) : ofFin (z : Fin (2 ^ w)) = ↑z := by
  cases w
  case zero =>
    simp only [eq_nil]
  case succ w =>
    apply BitVec.eq_of_toInt_eq
    rw [toInt_ofFin, Fin.val_intCast, Int.natCast_pow, Nat.cast_ofNat, Int.ofNat_toNat,
      toInt_intCast]
    rw [Int.max_eq_left]
    · have h : (2 ^ (w + 1) : Int) = (2 ^ (w + 1) : Nat) := by simp
      rw [h, Int.emod_bmod]
    · omega

open Fin.CommRing in
