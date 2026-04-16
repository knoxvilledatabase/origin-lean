/-
Extracted from Tactic/Check.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Elab.Tactic.Basic
import Lean.PrettyPrinter
import Lean.Elab.SyntheticMVars

noncomputable section

/-!
# `#check` tactic

This module defines a tactic version of the `#check` command.
While `#check t` is similar to `have := t`, it is a little more convenient
since it elaborates `t` in a more tolerant way and so it can be possible to get a result.
For example, `#check` allows metavariables.
-/

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

def elabCheckTactic (tk : Syntax) (ignoreStuckTC : Bool) (term : Term) : TacticM Unit :=
  withoutModifyingStateWithInfoAndMessages <| withMainContext do
    if let `($_:ident) := term then
      -- show signature for `#check ident`
      try
        for c in (← realizeGlobalConstWithInfos term) do
          addCompletionInfo <| .id term c (danglingDot := false) {} none
          logInfoAt tk <| MessageData.signature c
          return
      catch _ => pure ()  -- identifier might not be a constant but constant + projection
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := ignoreStuckTC)
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    let type ← inferType e
    if e.isSyntheticSorry then
      return
    logInfoAt tk m!"{e} : {type}"

elab tk:"#check " colGt term:term : tactic => elabCheckTactic tk true term

end Mathlib.Tactic
