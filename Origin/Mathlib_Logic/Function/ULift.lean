/-
Extracted from Logic/Function/ULift.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `ULift` and `PLift`
-/

theorem ULift.down_injective {α : Type*} : Function.Injective (@ULift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr
