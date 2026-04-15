/-
Extracted from Data/DFinsupp/Lex.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Lexicographic order on finitely supported dependent functions

This file defines the lexicographic order on `DFinsupp`.
-/

variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

section Zero

variable [∀ i, Zero (α i)]

protected def Lex (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) (x y : Π₀ i, α i) : Prop :=
  Pi.Lex r (s _) x y

theorem lex_def {r : ι → ι → Prop} {s : ∀ i, α i → α i → Prop} {a b : Π₀ i, α i} :
    DFinsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s j (a j) (b j) :=
  .rfl

-- INSTANCE (free from Core): [LT

-- INSTANCE (free from Core): [LT

theorem Lex.lt_iff [LT ι] [∀ i, LT (α i)] {a b : Lex (Π₀ i, α i)} :
    a < b ↔ ∃ i, (∀ j, j < i → a j = b j) ∧ a i < b i :=
  .rfl
