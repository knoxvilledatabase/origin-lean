/-
Extracted from Logic/Function/ULift.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Logic.Function.Defs

/-!
# `ULift` and `PLift`
-/

theorem ULift.down_injective {α : Sort _} : Function.Injective (@ULift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr

@[simp] theorem ULift.down_inj {α : Sort _} {a b : ULift α} : a.down = b.down ↔ a = b :=
  ⟨fun h ↦ ULift.down_injective h, fun h ↦ by rw [h]⟩

variable {α : Sort*}

theorem PLift.down_injective : Function.Injective (@PLift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr

@[simp] theorem PLift.down_inj {a b : PLift α} : a.down = b.down ↔ a = b :=
  ⟨fun h ↦ PLift.down_injective h, fun h ↦ by rw [h]⟩
