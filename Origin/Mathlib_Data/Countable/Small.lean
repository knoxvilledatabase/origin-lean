/-
Extracted from Data/Countable/Small.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# All countable types are small.

That is, any countable type is equivalent to a type in any universe.
-/

universe w v

-- INSTANCE (free from Core): (priority

theorem Uncountable.of_not_small {α : Type v} (h : ¬ Small.{w} α) : Uncountable α := by
  rw [uncountable_iff_not_countable]
  exact mt (@Countable.toSmall α) h
