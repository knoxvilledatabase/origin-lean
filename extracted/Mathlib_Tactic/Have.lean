/-
Extracted from Tactic/Have.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars
import Lean.Meta.Tactic.Assert

noncomputable section

/-!
# Extending `have`, `let` and `suffices`

This file extends the `have`, `let` and `suffices` tactics to allow the addition of hypotheses to
the context without requiring their proofs to be provided immediately.

As a style choice, this should not be used in mathlib; but is provided for downstream users who
preferred the old style.
-/

namespace Mathlib.Tactic

open Lean Elab.Tactic Meta Parser Term Syntax.MonadTraverser

def optBinderIdent : Parser := leading_parser
  -- Note: the withResetCache is because leading_parser seems to add a cache boundary,
  -- which causes the `hygieneInfo` parser not to be able to undo the trailing whitespace
  (ppSpace >> Term.binderIdent) <|> withResetCache hygieneInfo

def optBinderIdent.name (id : TSyntax ``optBinderIdent) : Name :=
  if id.raw[0].isIdent then id.raw[0].getId else HygieneInfo.mkIdent ⟨id.raw[0]⟩ `this |>.getId

def haveIdLhs' : Parser :=
  optBinderIdent >> many (ppSpace >>
    checkColGt "expected to be indented" >> letIdBinder) >> optType

syntax "have" haveIdLhs' : tactic

syntax "let " haveIdLhs' : tactic

syntax "suffices" haveIdLhs' : tactic

open Elab Term in

def haveLetCore (goal : MVarId) (name : TSyntax ``optBinderIdent)
    (bis : Array (TSyntax ``letIdBinder))
    (t : Option Term) (keepTerm : Bool) : TermElabM (MVarId × MVarId) :=
  let declFn := if keepTerm then MVarId.define else MVarId.assert
  goal.withContext do
    let n := optBinderIdent.name name
    let elabBinders k := if bis.isEmpty then k #[] else elabBinders bis k
    let (goal1, t, p) ← elabBinders fun es ↦ do
      let t ← match t with
      | none => mkFreshTypeMVar
      | some stx => withRef stx do
        let e ← Term.elabType stx
        Term.synthesizeSyntheticMVars (postpone := .no)
        instantiateMVars e
      let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
      pure (p.mvarId!, ← mkForallFVars es t, ← mkLambdaFVars es p)
    let (fvar, goal2) ← (← declFn goal n t p).intro1P
    goal2.withContext do
      Term.addTermInfo' (isBinder := true) name.raw[0] (mkFVar fvar)
    pure (goal1, goal2)

elab_rules : tactic

| `(tactic| have $n:optBinderIdent $bs* $[: $t:term]?) => do

  let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t false

  replaceMainGoal [goal1, goal2]

elab_rules : tactic

| `(tactic| suffices $n:optBinderIdent $bs* $[: $t:term]?) => do

  let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t false

  replaceMainGoal [goal2, goal1]

elab_rules : tactic

| `(tactic| let $n:optBinderIdent $bs* $[: $t:term]?) => withMainContext do

  let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t true

  replaceMainGoal [goal1, goal2]

end Mathlib.Tactic
