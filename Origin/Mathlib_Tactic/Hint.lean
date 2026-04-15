/-
Extracted from Tactic/Hint.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Meta.Tactic.TryThis
import Batteries.Linter.UnreachableTactic
import Batteries.Control.Nondet.Basic
import Mathlib.Tactic.FailIfNoProgress

/-!
# The `hint` tactic.

The `hint` tactic tries the kitchen sink:
it runs every tactic registered via the `register_hint tac` command
on the current goal, and reports which ones succeed.

## Future work
It would be nice to run the tactics in parallel.
-/

open Lean Elab Tactic

open Lean.Meta.Tactic.TryThis

namespace Mathlib.Tactic.Hint

initialize hintExtension : SimplePersistentEnvExtension (TSyntax `tactic) (List (TSyntax `tactic)) ←

  registerSimplePersistentEnvExtension {

    addEntryFn := (·.cons)

    addImportedFn := mkStateFromImportedEntries (·.cons) {}

  }

def addHint (stx : TSyntax `tactic) : CoreM Unit := do
  modifyEnv fun env => hintExtension.addEntry env stx

def getHints : CoreM (List (TSyntax `tactic)) := return hintExtension.getState (← getEnv)

open Lean.Elab.Command in

elab (name := registerHintStx) "register_hint" tac:tactic : command => liftTermElabM do

  let tac : TSyntax `tactic := ⟨tac.raw.copyHeadTailInfoFrom .missing⟩

  addHint tac

initialize

  Batteries.Linter.UnreachableTactic.ignoreTacticKindsRef.modify fun s => s.insert ``registerHintStx

def suggestion (tac : TSyntax `tactic) (msgs : MessageLog := {}) : TacticM Suggestion := do
  -- TODO `addExactSuggestion` has an option to construct `postInfo?`
  -- Factor that out so we can use it here instead of copying and pasting?
  let goals ← getGoals
  let postInfo? ← if goals.isEmpty then pure none else
    let mut str := "\nRemaining subgoals:"
    for g in goals do
      let e ← PrettyPrinter.ppExpr (← instantiateMVars (← g.getType))
      str := str ++ Format.pretty ("\n⊢ " ++ e)
    pure (some str)
  let style? := if goals.isEmpty then some .success else none
  let msg? ← msgs.toList.findM? fun m => do pure <|
    m.severity == MessageSeverity.information && (← m.data.toString).startsWith "Try this: "
  let suggestion ← match msg? with
  | some m => pure <| SuggestionText.string (((← m.data.toString).drop 10).takeWhile (· != '\n'))
  | none => pure <| SuggestionText.tsyntax tac
  return { suggestion, postInfo?, style? }

def withMessageLog (t : TacticM Unit) : TacticM MessageLog := do
  let initMsgs ← modifyGetThe Core.State fun st => (st.messages, { st with messages := {} })
  t
  modifyGetThe Core.State fun st => (st.messages, { st with messages := initMsgs })

def withoutInfoTrees (t : TacticM Unit) : TacticM Unit := do
  let trees := (← getInfoState).trees
  t
  modifyInfoState fun s => { s with trees }

def hint (stx : Syntax) : TacticM Unit := do
  let tacs := Nondet.ofList (← getHints)
  let results := tacs.filterMapM fun t : TSyntax `tactic => do
    if let some msgs ← observing? (withMessageLog (withoutInfoTrees (evalTactic t))) then
      return some (← getGoals, ← suggestion t msgs)
    else
      return none
  let results ← (results.toMLList.takeUpToFirst fun r => r.1.1.isEmpty).asArray
  let results := results.qsort (·.1.1.length < ·.1.1.length)
  addSuggestions stx (results.map (·.1.2))
  match results.find? (·.1.1.isEmpty) with
  | some r =>
    -- We don't restore the entire state, as that would delete the suggestion messages.
    setMCtx r.2.term.meta.meta.mctx
  | none => admitGoal (← getMainGoal)

syntax (name := hintStx) "hint" : tactic

elab_rules : tactic

  | `(tactic| hint%$tk) => hint tk

end Mathlib.Tactic.Hint
