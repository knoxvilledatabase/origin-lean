/-
Extracted from Data/Set/Countable.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Countable sets

In this file we define `Set.Countable s` as `Countable s`
and prove basic properties of this definition.

Note that this definition does not provide a computable encoding.
For a noncomputable conversion to `Encodable s`, use `Set.Countable.nonempty_encodable`.

## Keywords

sets, countable set
-/

assert_not_exists Monoid Multiset.sort

noncomputable section

open Function Set Encodable

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

namespace Set

protected def Countable (s : Set α) : Prop := Countable s
