/-
Extracted from Data/Quot.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Quotient types

This module extends the core library's treatment of quotient types (`Init.Core`).

## Tags

quotient
-/

variable {α : Sort*} {β : Sort*}

namespace Setoid

run_cmd Lean.Elab.Command.liftTermElabM do

  Lean.Meta.registerCoercion ``Setoid.r

    (some { numArgs := 2, coercee := 1, type := .coeFun })

-- INSTANCE (free from Core): :

theorem ext {α : Sort*} : ∀ {s t : Setoid α}, (∀ a b, s a b ↔ t a b) → s = t
  | ⟨r, _⟩, ⟨p, _⟩, Eq =>
  by have : r = p := funext fun a ↦ funext fun b ↦ propext <| Eq a b
     subst this
     rfl

end Setoid

namespace Quot

variable {ra : α → α → Prop} {rb : β → β → Prop} {φ : Quot ra → Quot rb → Sort*}
