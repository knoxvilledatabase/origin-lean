/-
Extracted from Lean/Thunk.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core
import Mathlib.Init

noncomputable section

/-!
# Basic facts about `Thunk`.
-/

namespace Thunk

universe u v

variable {α : Type u} {β : Type v}

instance [DecidableEq α] : DecidableEq (Thunk α) := by
  intro a b
  have : a = b ↔ a.get = b.get := ⟨by intro x; rw [x], by intro; ext; assumption⟩
  rw [this]
  infer_instance

def prod (a : Thunk α) (b : Thunk β) : Thunk (α × β) := Thunk.mk fun _ => (a.get, b.get)

def add [Add α] (a b : Thunk α) : Thunk α := Thunk.mk fun _ => a.get + b.get

instance [Add α] : Add (Thunk α) := ⟨add⟩

end Thunk
