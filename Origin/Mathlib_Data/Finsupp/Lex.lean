/-
Extracted from Data/Finsupp/Lex.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `Finsupp`.
-/

variable {α N : Type*}

namespace Finsupp

section NHasZero

variable [Zero N]

protected def Lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
  Pi.Lex r s x y

theorem lex_def {r : α → α → Prop} {s : N → N → Prop} {a b : α →₀ N} :
    Finsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s (a j) (b j) :=
  .rfl

-- INSTANCE (free from Core): [LT

-- INSTANCE (free from Core): [LT

theorem Lex.lt_iff [LT α] [LT N] {a b : Lex (α →₀ N)} :
    a < b ↔ ∃ i, (∀ j, j < i → a j = b j) ∧ a i < b i :=
  .rfl
