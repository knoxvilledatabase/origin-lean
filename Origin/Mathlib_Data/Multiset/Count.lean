/-
Extracted from Data/Multiset/Count.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Counting multiplicity in a multiset

-/

assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

variable (p : α → Prop) [DecidablePred p]

/-! ### countP -/

def countP (s : Multiset α) : ℕ :=
  Quot.liftOn s (List.countP p) fun _l₁ _l₂ => Perm.countP_eq (p ·)
