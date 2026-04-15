/-
Extracted from Logic/ExistsUnique.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `ExistsUnique`

This file defines the `ExistsUnique` predicate, notated as `∃!`, and proves some of its
basic properties.
-/

variable {α : Sort*}

def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

namespace Mathlib.Notation

open Lean

meta def isExplicitBinderSingular (xs : TSyntax ``explicitBinders) : Bool :=
  match xs with
  | `(explicitBinders| $_:binderIdent $[: $_]?) => true
  | `(explicitBinders| ($_:binderIdent : $_)) => true
  | _ => false

open TSyntax.Compat in

macro "∃!" xs:explicitBinders ", " b:term : term => do

  if !isExplicitBinderSingular xs then

    Macro.throwErrorAt xs "\

      The `ExistsUnique` notation should not be used with more than one binder.\n\

      \n\

      The reason for this is that `∃! (x : α), ∃! (y : β), p x y` has a completely different \

      meaning from `∃! q : α × β, p q.1 q.2`. \

      To prevent confusion, this notation requires that you be explicit \

      and use one with the correct interpretation."

  expandExplicitBinders ``ExistsUnique xs b
