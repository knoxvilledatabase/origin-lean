/-
Extracted from GroupTheory/GroupAction/IterateAct.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monoid action by iterates of a map

In this file we define `IterateMulAct f`, `f : α → α`, as a one field structure wrapper over `ℕ`
that acts on `α` by iterates of `f`, `⟨n⟩ • x = f^[n] x`.

It is useful to convert between definitions and theorems about maps and monoid actions.
-/

structure IterateAddAct {α : Type*} (f : α → α) where
  /-- The value of `n : IterateAddAct f`. -/
  val : ℕ
