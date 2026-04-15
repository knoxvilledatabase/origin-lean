/-
Extracted from Data/Fin/Parity.lean
Genuine: 6 of 14 | Dissolved: 8 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Defs

/-!
# Parity in `Fin n`

In this file we prove that an element `k : Fin n` is even in `Fin n`
iff `n` is odd or `Fin.val k` is even.
-/

open Fin

namespace Fin

lemma even_of_val {n : ℕ} {k : Fin n} (h : Even k.val) : Even k := by
  have : NeZero n := ⟨k.pos.ne'⟩
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

-- DISSOLVED: odd_of_val

lemma even_of_odd {n : ℕ} (hn : Odd n) (k : Fin n) : Even k := by
  have : NeZero n := ⟨k.pos.ne'⟩
  rcases k.val.even_or_odd with hk | hk
  · exact even_of_val hk
  · simpa using (hk.add_odd hn).natCast (α := Fin n)

-- DISSOLVED: odd_of_odd

lemma even_iff_of_even {n : ℕ} (hn : Even n) {k : Fin n} : Even k ↔ Even k.val := by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, even_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add_eq_ite]
  split_ifs with h <;> simp [Nat.even_sub, *]

-- DISSOLVED: odd_iff_of_even

lemma even_iff {n : ℕ} {k : Fin n} : Even k ↔ (Odd n ∨ Even k.val) := by
  refine ⟨fun hk ↦ ?_, or_imp.mpr ⟨(even_of_odd · k), even_of_val⟩⟩
  rw [← Nat.not_even_iff_odd, ← imp_iff_not_or]
  exact fun hn ↦ (even_iff_of_even hn).mp hk

lemma even_iff_imp {n : ℕ} {k : Fin n} : Even k ↔ (Even n → Even k.val) := by
  rw [imp_iff_not_or, Nat.not_even_iff_odd]
  exact even_iff

-- DISSOLVED: odd_iff

-- DISSOLVED: odd_iff_imp

lemma even_iff_mod_of_even {n : ℕ} (hn : Even n) {k : Fin n} : Even k ↔ k.val % 2 = 0 := by
  rw [even_iff_of_even hn]
  exact Nat.even_iff

-- DISSOLVED: odd_iff_mod_of_even

-- DISSOLVED: not_odd_iff_even_of_even

-- DISSOLVED: not_even_iff_odd_of_even

end Fin
