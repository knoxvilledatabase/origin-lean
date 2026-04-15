/-
Extracted from Order/Circular/ZMod.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The circular order on `ZMod n`

This file defines the circular order on `ZMod n`.
-/

-- INSTANCE (free from Core): :

variable {a b c : ℤ}

lemma Int.btw_iff : btw a b c ↔ a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b := .rfl

lemma Int.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl

-- INSTANCE (free from Core): (n

variable {n : ℕ} {a b c : Fin n}

lemma Fin.btw_iff : btw a b c ↔ a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b := .rfl

lemma Fin.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl

-- INSTANCE (free from Core): :
