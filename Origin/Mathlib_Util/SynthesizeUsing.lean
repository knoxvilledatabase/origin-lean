/-
Extracted from Util/SynthesizeUsing.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Elab.Tactic.Basic
import Qq

/-!
# `SynthesizeUsing`

This is a slight simplification of the `solve_aux` tactic in Lean3.
-/

open Lean Elab Tactic Meta Qq

def synthesizeUsing {u : Level} (type : Q(Sort u)) (tac : TacticM Unit) :
    MetaM (List MVarId × Q($type)) := do
  let m ← mkFreshExprMVar type
  let goals ← (Term.withoutErrToSorry <| run m.mvarId! tac).run'
  return (goals, ← instantiateMVars m)

def synthesizeUsing' {u : Level} (type : Q(Sort u)) (tac : TacticM Unit) : MetaM Q($type) := do
  let (goals, e) ← synthesizeUsing type tac
  -- Note: doesn't use `tac *> Tactic.done` since that just adds a message
  -- rather than raising an error.
  unless goals.isEmpty do
    throwError m!"synthesizeUsing': unsolved goals\n{goalsToMessageData goals}"
  return e

def synthesizeUsingTactic {u : Level} (type : Q(Sort u)) (tac : Syntax) :
    MetaM (List MVarId × Q($type)) := do
  synthesizeUsing type (do evalTactic tac)

def synthesizeUsingTactic' {u : Level} (type : Q(Sort u)) (tac : Syntax) : MetaM Q($type) := do
  synthesizeUsing' type (do evalTactic tac)
