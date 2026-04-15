/-
Extracted from Data/Fin/Pigeonhole.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pigeonhole-like results for Fin

This adapts Pigeonhole-like results from `Mathlib.Data.Fintype.Card` to the setting where the map
has the type `f : Fin m → Fin n`.
-/

namespace Fin

variable {m n : ℕ}

theorem le_of_injective (f : Fin m → Fin n) (hf : f.Injective) : m ≤ n := by
  simpa using Fintype.card_le_of_injective f hf

theorem le_of_embedding (f : Fin m ↪ Fin n) : m ≤ n := by
  simpa using Fintype.card_le_of_embedding f

theorem lt_of_injective_of_notMem (f : Fin m → Fin n) (hf : f.Injective) {b : Fin n}
    (hb : b ∉ Set.range f) : m < n := by
  simpa using Fintype.card_lt_of_injective_of_notMem f hf hb

theorem le_of_surjective (f : Fin m → Fin n) (hf : Function.Surjective f) : n ≤ m := by
  simpa using Fintype.card_le_of_surjective f hf

theorem card_range_le {α : Type*} [Fintype α] [DecidableEq α] (f : Fin m → α) :
    Fintype.card (Set.range f) ≤ m := by
  simpa using Fintype.card_range_le f

end Fin
