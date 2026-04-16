/-
Extracted from Data/Bool/AllAny.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar

noncomputable section

/-!
# Boolean quantifiers

This proves a few properties about `List.all` and `List.any`, which are the `Bool` universal and
existential quantifiers. Their definitions are in core Lean.
-/

variable {α : Type*} {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

namespace List

theorem any_of_mem {p : α → Bool} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
  any_eq_true.2 ⟨_, h₁, h₂⟩

end List
