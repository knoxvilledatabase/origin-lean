/-
Extracted from Data/Set/Accumulate.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Accumulate

The function `accumulate` takes `s : α → Set β` with `LE α` and returns `⋃ y ≤ x, s y`.
It is related to `dissipate s := ⋂ y ≤ x, s y`.

`accumulate` is closely related to the function `partialSups`, although these two functions have
slightly different typeclass assumptions and API. `partialSups_eq_accumulate` shows
that they coincide on `ℕ`.
-/

variable {α β : Type*} {s : α → Set β}

namespace Set

def accumulate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋃ y ≤ x, s y
