/-
Extracted from Data/Set/Opposite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The opposite of a set

The opposite of a set `s` is simply the set obtained by taking the opposite of each member of `s`.
-/

variable {α : Type*}

open Opposite

namespace Set

protected def op (s : Set α) : Set αᵒᵖ :=
  unop ⁻¹' s

protected def unop (s : Set αᵒᵖ) : Set α :=
  op ⁻¹' s
