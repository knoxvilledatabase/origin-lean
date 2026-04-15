/-
Extracted from Data/Finset/NAry.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# N-ary images of finsets

This file defines `Finset.image₂`, the binary image of finsets. This is the finset version of
`Set.image2`. This is mostly useful to define pointwise operations.

## Notes

This file is very similar to `Mathlib/Data/Set/NAry.lean`, `Mathlib/Order/Filter/NAry.lean` and
`Mathlib/Data/Option/NAry.lean`. Please keep them in sync.

We do not define `Finset.image₃` as its only purpose would be to prove properties of `Finset.image₂`
and `Set.image2` already fulfills this task.
-/

open Function Set

variable {α α' β β' γ γ' δ δ' ε ε' ζ ζ' ν : Type*}

namespace Finset

variable [DecidableEq α'] [DecidableEq β'] [DecidableEq γ] [DecidableEq γ']
  [DecidableEq δ'] [DecidableEq ε] [DecidableEq ε'] {f f' : α → β → γ} {g g' : α → β → γ → δ}
  {s s' : Finset α} {t t' : Finset β} {u u' : Finset γ} {a a' : α} {b b' : β} {c : γ}

def image₂ (f : α → β → γ) (s : Finset α) (t : Finset β) : Finset γ :=
  (s ×ˢ t).image <| uncurry f
