/-
Extracted from Data/Set/Semiring.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sets as a semiring under union

This file defines `SetSemiring α`, an alias of `Set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `SetSemiring α` is a
(commutative) semiring.
-/

open Function Set

open Pointwise

variable {α β : Type*}

def SetSemiring (α : Type*) : Type _ :=
  Set α

deriving Inhabited, PartialOrder, OrderBot

protected def Set.up : Set α ≃ SetSemiring α :=
  Equiv.refl _

namespace SetSemiring

protected def down : SetSemiring α ≃ Set α :=
  Equiv.refl _

open SetSemiring (down)

open Set (up)
