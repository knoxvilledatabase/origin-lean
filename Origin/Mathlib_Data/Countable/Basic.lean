/-
Extracted from Data/Countable/Basic.lean
Genuine: 5 of 16 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core

/-!
# Countable types

In this file we provide basic instances of the `Countable` typeclass defined elsewhere.
-/

assert_not_exists Monoid

universe u v w

open Function

-- INSTANCE (free from Core): :

/-!
### Definition in terms of `Function.Embedding`
-/

section Embedding

variable {α : Sort u} {β : Sort v}

theorem countable_iff_nonempty_embedding : Countable α ↔ Nonempty (α ↪ ℕ) :=
  ⟨fun ⟨⟨f, hf⟩⟩ => ⟨⟨f, hf⟩⟩, fun ⟨f⟩ => ⟨⟨f, f.2⟩⟩⟩

theorem uncountable_iff_isEmpty_embedding : Uncountable α ↔ IsEmpty (α ↪ ℕ) := by
  rw [← not_countable_iff, countable_iff_nonempty_embedding, not_nonempty_iff]

theorem nonempty_embedding_nat (α) [Countable α] : Nonempty (α ↪ ℕ) :=
  countable_iff_nonempty_embedding.1 ‹_›

protected theorem Function.Embedding.countable [Countable β] (f : α ↪ β) : Countable α :=
  f.injective.countable

protected lemma Function.Embedding.uncountable [Uncountable α] (f : α ↪ β) : Uncountable β :=
  f.injective.uncountable

end Embedding

/-!
### Operations on `Type*`s
-/

section type

variable {α : Type u} {β : Type v} {π : α → Type w}

-- INSTANCE (free from Core): [Countable

-- INSTANCE (free from Core): Sum.uncountable_inl

-- INSTANCE (free from Core): Sum.uncountable_inr

-- INSTANCE (free from Core): Option.instCountable

-- INSTANCE (free from Core): WithTop.instCountable

-- INSTANCE (free from Core): WithBot.instCountable

-- INSTANCE (free from Core): ENat.instCountable

-- INSTANCE (free from Core): Option.instUncountable

-- INSTANCE (free from Core): WithTop.instUncountable

-- INSTANCE (free from Core): WithBot.instUncountable
