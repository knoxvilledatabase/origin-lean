/-
Extracted from Tactic/Widget/GCongr.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.Widget.SelectPanelUtils
import Mathlib.Tactic.GCongr

/-! # GCongr widget

This file defines a `gcongr?` tactic that displays a widget panel allowing to generate
a `gcongr` call with holes specified by selecting subexpressions in the goal.
-/

open Lean Meta Server ProofWidgets

@[nolint unusedArguments]
def makeGCongrString (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
    (_ : SelectInsertParams) : MetaM (String × String × Option (String.Pos × String.Pos)) := do

let subexprPos := getGoalLocations pos

unless goalType.isAppOf ``LE.le || goalType.isAppOf ``LT.lt || goalType.isAppOf `Int.ModEq do

  panic! "The goal must be a ≤ or < or ≡."

let mut goalTypeWithMetaVars := goalType

for pos in subexprPos do

  goalTypeWithMetaVars ← insertMetaVar goalTypeWithMetaVars pos

let side := if goalType.isAppOf `Int.ModEq then

              if subexprPos[0]!.toArray[0]! = 0 then 1 else 2

            else

              if subexprPos[0]!.toArray[0]! = 0 then 2 else 3

let sideExpr := goalTypeWithMetaVars.getAppArgs[side]!

let res := "gcongr " ++ (toString (← Meta.ppExpr sideExpr)).renameMetaVar

return (res, res, none)

@[server_rpc_method]
def GCongrSelectionPanel.rpc := mkSelectionPanelRPC makeGCongrString
  "Use shift-click to select sub-expressions in the goal that should become holes in gcongr."
  "GCongr 🔍"

@[widget_module]
def GCongrSelectionPanel : Component SelectInsertParams :=
  mk_rpc_widget% GCongrSelectionPanel.rpc

open scoped Json in

elab stx:"gcongr?" : tactic => do

  let some replaceRange := (← getFileMap).rangeOfStx? stx | return

  Widget.savePanelWidgetInfo GCongrSelectionPanel.javascriptHash

    (pure <| json% { replaceRange: $(replaceRange) }) stx
