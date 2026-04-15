/-
Extracted from Data/Opposite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Opposites

In this file we define a structure `Opposite α` containing a single field of type `α` and
two bijections `op : α → αᵒᵖ` and `unop : αᵒᵖ → α`. If `α` is a category, then `αᵒᵖ` is the
opposite category, with all arrows reversed.

-/

universe v u

variable (α : Sort u)

structure Opposite where
  /-- The canonical map `α → αᵒᵖ`. -/
  op ::
  /-- The canonical map `αᵒᵖ → α`. -/
  unop : α

attribute [pp_nodot] Opposite.unop
