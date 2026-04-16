/-
Extracted from Std/Data/HashMap.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Std.Data.HashMap.Basic
import Mathlib.Init

noncomputable section

/-!
# Convenience functions for hash maps

These will be reimplemented in the Lean standard library.
-/

namespace Std.HashMap

variable {α β γ : Type _} [BEq α] [Hashable α]

def mapVal (f : α → β → γ) (m : HashMap α β) : HashMap α γ :=
  m.fold (fun acc k v => acc.insert k (f k v)) HashMap.empty

end Std.HashMap
