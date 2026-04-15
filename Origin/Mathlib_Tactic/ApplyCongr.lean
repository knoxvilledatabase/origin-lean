/-
Extracted from Tactic/ApplyCongr.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.Conv

/-!
## Introduce the `apply_congr` conv mode tactic.

`apply_congr` will apply congruence lemmas inside `conv` mode.
It is particularly useful when the automatically generated congruence lemmas
are not of the optimal shape. An example, described in the doc-string is
rewriting inside the operand of a `Finset.sum`.
-/

open Lean Expr Parser.Tactic Elab Command Elab.Tactic Meta Conv

def Lean.Elab.Tactic.applyCongr (q : Option Expr) : TacticM Unit := do
  let const lhsFun _ ← (getAppFn ∘ cleanupAnnotations) <$> instantiateMVars (← getLhs) |
    throwError "Left-hand side must be an application of a constant."
  let congrTheoremExprs ←
    match q with
    -- If the user specified a lemma, use that one,
    | some e =>
      pure [e]
    -- otherwise, look up everything tagged `@[congr]`
    | none =>
      let congrTheorems ←
        (fun congrTheoremMap => congrTheoremMap.get lhsFun) <$> getSimpCongrTheorems
      congrTheorems.mapM (fun congrTheorem =>
        liftM <| mkConstWithFreshMVarLevels congrTheorem.theoremName)
  if congrTheoremExprs == [] then
    throwError "No matching congr lemmas found"
  -- For every lemma:
  liftMetaTactic fun mainGoal => congrTheoremExprs.firstM (fun congrTheoremExpr => do
    let newGoals ← mainGoal.apply congrTheoremExpr { newGoals := .nonDependentOnly }
    newGoals.mapM fun newGoal => Prod.snd <$> newGoal.intros)

syntax (name := Lean.Parser.Tactic.applyCongr) "apply_congr" (ppSpace colGt term)? : conv

elab_rules : conv

  | `(conv| apply_congr$[ $t?]?) => do

    let e? ← t?.mapM (fun t => elabTerm t.raw none)

    applyCongr e?
