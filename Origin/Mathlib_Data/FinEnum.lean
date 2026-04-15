/-
Extracted from Data/FinEnum.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
Type class for finitely enumerable types. The property is stronger
than `Fintype` in that it assigns each element a rank in a finite
enumeration.
-/

universe u v

open Finset

class FinEnum (α : Sort*) where
  /-- `FinEnum.card` is the cardinality of the `FinEnum` -/
  card : ℕ
  /-- `FinEnum.Equiv` states that type `α` is in bijection with `Fin card`,
  the size of the `FinEnum` -/
  equiv : α ≃ Fin card
  [decEq : DecidableEq α]

-- INSTANCE (free from Core): 100]

namespace FinEnum

variable {α : Type u} {β : α → Type v}
