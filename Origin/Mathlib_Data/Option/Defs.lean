/-
Extracted from Data/Option/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Mathlib/Data/Option/`.
Other basic operations on `Option` are defined in the core library.
-/

namespace Option

protected def traverse.{u, v}
    {F : Type u → Type v} [Applicative F] {α : Type*} {β : Type u} (f : α → F β) :
    Option α → F (Option β) := Option.mapA f

variable {α : Type*} {β : Type*}

protected def elim' (b : β) (f : α → β) : Option α → β
  | some a => f a
  | none => b
