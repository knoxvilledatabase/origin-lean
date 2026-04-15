/-
Extracted from Data/Vector/Defs.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
The type `List.Vector` represents lists with fixed length.

TODO: The API of `List.Vector` is quite incomplete relative to `Vector`,
and in particular does not use `x[i]` (that is `GetElem` notation) as the preferred accessor.
Any combination of reducing the use of `List.Vector` in Mathlib, or modernising its API,
would be welcome.
-/

assert_not_exists Monoid

universe u v w

def List.Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }

namespace List.Vector

variable {α β σ φ : Type*} {n : ℕ} {p : α → Prop}

-- INSTANCE (free from Core): [DecidableEq
