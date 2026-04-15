/-
Extracted from Order/RelClasses.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Unbundled relation classes

In this file we prove some properties of `Is*` classes defined in
`Mathlib/Order/Defs/Unbundled.lean`.
The main difference between these classes and the usual order classes (`Preorder` etc) is that
usual classes extend `LE` and/or `LT` while these classes take a relation as an explicit argument.
-/

universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

open Function

theorem Std.Refl.swap (r : α → α → Prop) [Std.Refl r] : Std.Refl (swap r) :=
  ⟨refl_of r⟩
