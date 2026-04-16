/-
Extracted from Tactic/Contrapose.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.PushNeg

noncomputable section

/-! # Contrapose

The `contrapose` tactic transforms the goal into its contrapositive when that goal is an
implication.

* `contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`
* `contrapose!`    turns a goal `P → Q` into `¬ Q → ¬ P` and pushes negations inside `P` and `Q`
  using `push_neg`
* `contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose! h`  first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis

-/

namespace Mathlib.Tactic.Contrapose

lemma mtr {p q : Prop} : (¬ q → ¬ p) → (p → q) := fun h hp ↦ by_contra (fun h' ↦ h h' hp)

syntax (name := contrapose) "contrapose" (ppSpace colGt ident (" with " ident)?)? : tactic

macro_rules
  | `(tactic| contrapose) => `(tactic| (refine mtr ?_))
  | `(tactic| contrapose $e) => `(tactic| (revert $e:ident; contrapose; intro $e:ident))
  | `(tactic| contrapose $e with $e') => `(tactic| (revert $e:ident; contrapose; intro $e':ident))

syntax (name := contrapose!) "contrapose!" (ppSpace colGt ident (" with " ident)?)? : tactic

macro_rules
  | `(tactic| contrapose!) => `(tactic| (contrapose; try push_neg))
  | `(tactic| contrapose! $e) => `(tactic| (revert $e:ident; contrapose!; intro $e:ident))
  | `(tactic| contrapose! $e with $e') => `(tactic| (revert $e:ident; contrapose!; intro $e':ident))

end Mathlib.Tactic.Contrapose
