/-
Extracted from Data/Option/NAry.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Binary map of options

This file defines the binary map of `Option`. This is mostly useful to define pointwise operations
on intervals.

## Main declarations

* `Option.map₂`: Binary map of options.

## Notes

This file is very similar to the n-ary section of `Mathlib/Data/Set/Basic.lean`, to
`Mathlib/Data/Finset/NAry.lean` and to `Mathlib/Order/Filter/NAry.lean`. Please keep them in sync.

We do not define `Option.map₃` as its only purpose so far would be to prove properties of
`Option.map₂` and casing already fulfills this task.
-/

universe u

open Function

namespace Option

attribute [local grind cases] Option

variable {α β γ δ : Type*} {f : α → β → γ} {a : Option α} {b : Option β} {c : Option γ}

def map₂ (f : α → β → γ) (a : Option α) (b : Option β) : Option γ :=
  a.bind fun a => b.map <| f a

theorem map₂_def {α β γ : Type u} (f : α → β → γ) (a : Option α) (b : Option β) :
    map₂ f a b = f <$> a <*> b := by
  cases a <;> rfl
