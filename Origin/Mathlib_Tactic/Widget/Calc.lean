/-
Extracted from Tactic/Widget/Calc.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Elab.Tactic.Calc
import Mathlib.Data.String.Defs
import Mathlib.Tactic.Widget.SelectPanelUtils
import Batteries.CodeAction.Attr
import Batteries.Lean.Position

/-! # Calc widget

This file redefines the `calc` tactic so that it displays a widget panel allowing to create
new calc steps with holes specified by selected sub-expressions in the goal.
-/

section code_action

open Batteries.CodeAction

open Lean Server RequestM

@[tactic_code_action calcTactic]
def createCalc : TacticCodeAction := fun _params _snap ctx _stack node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  if info.goalsBefore.isEmpty then return #[]
  let eager := {
    title := s!"Generate a calc block."
    kind? := "quickfix"
  }
  let doc ← readDoc
  return #[{
    eager
    lazy? := some do
      let tacPos := doc.meta.text.utf8PosToLspPos info.stx.getPos?.get!
      let endPos := doc.meta.text.utf8PosToLspPos info.stx.getTailPos?.get!
      let goal := info.goalsBefore[0]!
      let goalFmt ← ctx.runMetaM {} <| goal.withContext do Meta.ppExpr (← goal.getType)
      return { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier
          { range := ⟨tacPos, endPos⟩, newText := s!"calc {goalFmt} := by sorry" }
      }
  }]

end code_action

open ProofWidgets

open Lean Meta

open Lean Server in

structure CalcParams extends SelectInsertParams where
  /-- Is this the first calc step? -/
  isFirst : Bool
  /-- indentation level of the calc block. -/
  indent : Nat
  deriving SelectInsertParamsClass, RpcEncodable

open Lean Meta

def suggestSteps (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) (params : CalcParams) :
    MetaM (String × String × Option (String.Pos × String.Pos)) := do
  let subexprPos := getGoalLocations pos
  let some (rel, lhs, rhs) ← Lean.Elab.Term.getCalcRelation? goalType |
      throwError "invalid 'calc' step, relation expected{indentExpr goalType}"
  let relApp := mkApp2 rel
    (← mkFreshExprMVar none)
    (← mkFreshExprMVar none)
  let some relStr := (← Meta.ppExpr relApp) |> toString |>.splitOn |>.get? 1
    | throwError "could not find relation symbol in {relApp}"
  let isSelectedLeft := subexprPos.any (fun L ↦ #[0, 1].isPrefixOf L.toArray)
  let isSelectedRight := subexprPos.any (fun L ↦ #[1].isPrefixOf L.toArray)

  let mut goalType := goalType
  for pos in subexprPos do
    goalType ← insertMetaVar goalType pos
  let some (_, newLhs, newRhs) ← Lean.Elab.Term.getCalcRelation? goalType | unreachable!

  let lhsStr := (toString <| ← Meta.ppExpr lhs).renameMetaVar
  let newLhsStr := (toString <| ← Meta.ppExpr newLhs).renameMetaVar
  let rhsStr := (toString <| ← Meta.ppExpr rhs).renameMetaVar
  let newRhsStr := (toString <| ← Meta.ppExpr newRhs).renameMetaVar

  let spc := String.replicate params.indent ' '
  let insertedCode := match isSelectedLeft, isSelectedRight with
  | true, true =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {newRhsStr} := by sorry\n\
         {spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newLhsStr} := by sorry\n{spc}\
         _ {relStr} {newRhsStr} := by sorry\n{spc}\
         _ {relStr} {rhsStr} := by sorry"
  | false, true =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newRhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newRhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
  | true, false =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
  | false, false => "This should not happen"

  let stepInfo := match isSelectedLeft, isSelectedRight with
  | true, true => "Create two new steps"
  | true, false | false, true => "Create a new step"
  | false, false => "This should not happen"
  let pos : String.Pos := insertedCode.find (fun c => c == '?')
  return (stepInfo, insertedCode, some (pos, ⟨pos.byteIdx + 2⟩) )

@[server_rpc_method]
def CalcPanel.rpc := mkSelectionPanelRPC suggestSteps
  "Please select subterms."
  "Calc 🔍"

@[widget_module]
def CalcPanel : Component CalcParams :=
  mk_rpc_widget% CalcPanel.rpc

namespace Lean.Elab.Tactic

open Meta

elab_rules : tactic

| `(tactic|calc%$calcstx $steps) => do

  let some calcRange := (← getFileMap).rangeOfStx? calcstx | unreachable!

  let indent := calcRange.start.character

  let mut isFirst := true

  for step in ← Lean.Elab.Term.mkCalcStepViews steps do

    let some replaceRange := (← getFileMap).rangeOfStx? step.ref | unreachable!

    let json := json% {"replaceRange": $(replaceRange),

                        "isFirst": $(isFirst),

                        "indent": $(indent)}

    Widget.savePanelWidgetInfo CalcPanel.javascriptHash (pure json) step.proof

    isFirst := false

  evalCalc (← `(tactic|calc%$calcstx $steps))

end Lean.Elab.Tactic
