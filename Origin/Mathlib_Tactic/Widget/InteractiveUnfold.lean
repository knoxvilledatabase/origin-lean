/-
Extracted from Tactic/Widget/InteractiveUnfold.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Batteries.Lean.Position
import Mathlib.Tactic.Widget.SelectPanelUtils
import Mathlib.Lean.GoalsLocation
import Mathlib.Lean.Meta.KAbstractPositions
import Lean.Util.FoldConsts

/-!

# Interactive unfolding

This file defines the interactive tactic `unfold?`.
It allows you to shift-click on an expression in the goal, and then it suggests rewrites to replace
the expression with an unfolded version.

It can be used on its own, but it can also be used as part of the library rewrite tactic `rw??`,
where these unfoldings are a subset of the suggestions.

For example, if the goal contains `1+1`, then it will suggest rewriting this into one of
- `Nat.add 1 1`
- `2`

Clicking on a suggestion pastes a rewrite into the editor, which will be of the form
- `rw [show 1+1 = Nat.add 1 1 from rfl]`
- `rw [show 1+1 = 2 from rfl]`
It also takes into account the position of the selected expression if it appears in multiple places,
and whether the rewrite is in the goal or a local hypothesis.
The rewrite string is created using `mkRewrite`.

## Reduction rules

The basic idea is to repeatedly apply `unfoldDefinition?` followed by `whnfCore`, which gives
the list of all suggested unfoldings. Each suggested unfolding is in `whnfCore` normal form.

Additionally, eta-reduction is tried, and basic natural number reduction is tried.

## Filtering

`HAdd.hAdd` in `1+1` actually first unfolds into `Add.add`, but this is not very useful,
because this is just unfolding a notational type class. Therefore, unfoldings of default instances
are not presented in the list of suggested rewrites.
This is implemented with `unfoldProjDefaultInst?`.

Additionally, we don't want to unfold into expressions involving `match` terms or other
constants marked as `Name.isInternalDetail`. So all such results are filtered out.
This is implemented with `isUserFriendly`.

-/

open Lean Meta Server Widget ProofWidgets Jsx

namespace Mathlib.Tactic.InteractiveUnfold

def unfoldProjDefaultInst? (e : Expr) : MetaM (Option Expr) := do
  let .const declName _ := e.getAppFn | return none
  let some { fromClass := true, ctorName, .. } ← getProjectionFnInfo? declName | return none
  -- get the list of default instances of the class
  let some (ConstantInfo.ctorInfo ci) := (← getEnv).find? ctorName | return none
  let defaults ← getDefaultInstances ci.induct
  if defaults.isEmpty then return none

  let some e ← withDefault <| unfoldDefinition? e | return none
  let .proj _ i c := e.getAppFn | return none
  -- check that the structure `c` comes from one of the default instances
  let .const inst _ := c.getAppFn | return none
  unless defaults.any (·.1 == inst) do return none

  let some r ← withReducibleAndInstances <| project? c i | return none
  return mkAppN r e.getAppArgs |>.headBeta

partial def unfolds (e : Expr) : MetaM (Array Expr) := do
  let e' ← whnfCore e
  go e' (if e == e' then #[] else #[e'])
where
  /-- Append the unfoldings of `e` to `acc`. Assume `e` is in `whnfCore` form. -/
  go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) :=
    tryCatchRuntimeEx
      (withIncRecDepth do
        if let some e := e.etaExpandedStrict? then
          let e ← whnfCore e
          return ← go e (acc.push e)
        if let some e ← reduceNat? e then
          return acc.push e
        if let some e ← reduceNative? e then
          return acc.push e
        if let some e ← unfoldProjDefaultInst? e then
          -- when unfolding a default instance, don't add it to the array of unfolds.
          let e ← whnfCore e
          return ← go e acc
        if let some e ← unfoldDefinition? e then
          -- Note: whnfCore can give a recursion depth error
          let e ← whnfCore e
          return ← go e (acc.push e)
        return acc)
      fun _ =>
        return acc

def isUserFriendly (e : Expr) : Bool :=
  !e.foldConsts (init := false) (fun name => (· || name.isInternalDetail))

def filteredUnfolds (e : Expr) : MetaM (Array Expr) :=
  return (← unfolds e).filter isUserFriendly

end InteractiveUnfold

def mkRewrite (occ : Option Nat) (symm : Bool) (rewrite : String) (loc : Option Name) : String :=
  let cfg := match occ with
    | some n => s! " (config := \{ occs := .pos [{n}]})"
    | none => ""
  let loc := match loc with
    | some n => s! " at {n}"
    | none => ""
  let symm := if symm then "← " else ""
  s! "rw{cfg} [{symm}{rewrite}]{loc}"

def pasteString (e : Expr) : MetaM String :=
  withOptions (fun _ => Options.empty
    |>.setBool `pp.universes false
    |>.setBool `pp.unicode.fun true) do
  return Format.pretty (← Meta.ppExpr e) (width := 90) (indent := 2)

namespace InteractiveUnfold

def tacticString (e unfold : Expr) (occ : Option Nat) (loc : Option Name) : MetaM String := do
  let rfl := s! "show {← pasteString (← mkEq e unfold)} from rfl"
  return mkRewrite occ false rfl loc

def renderUnfolds (e : Expr) (occ : Option Nat) (loc : Option Name) (range : Lsp.Range)
    (doc : FileWorker.EditableDocument) : MetaM (Option Html) := do
  let results ← filteredUnfolds e
  if results.isEmpty then
    return none
  let core ← results.mapM fun unfold => do
    let tactic ← tacticString e unfold occ loc
    return <li> {
      .element "p" #[] <|
        #[<span className="font-code" style={json% { "white-space" : "pre-wrap" }}> {
          Html.ofComponent MakeEditLink
            (.ofReplaceRange doc.meta range tactic)
            #[.text <| Format.pretty <| (← Meta.ppExpr unfold)] }
        </span>]
      } </li>
  return <details «open»={true}>
    <summary className="mv2 pointer">
      {.text "Definitional rewrites:"}
    </summary>
    {.element "ul" #[("style", json% { "padding-left" : "30px"})] core}
  </details>

@[server_rpc_method_cancellable]
private def rpc (props : SelectInsertParams) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let doc ← RequestM.readDoc
  let some loc := props.selectedLocations.back? |
    return .text "unfold?: Please shift-click an expression."
  if loc.loc matches .hypValue .. then
    return .text "unfold? doesn't work on the value of a let-bound free variable."
  let some goal := props.goals[0]? |
    return .text "There is no goal to solve!"
  if loc.mvarId != goal.mvarId then
    return .text "The selected expression should be in the main goal."
  goal.ctx.val.runMetaM {} do
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      let rootExpr ← loc.rootExpr
      let some (subExpr, occ) ← viewKAbstractSubExpr rootExpr loc.pos |
        return .text "expressions with bound variables are not supported"
      unless ← kabstractIsTypeCorrect rootExpr subExpr loc.pos do
        return .text <| "The selected expression cannot be rewritten, because the motive is " ++
          "not type correct. This usually occurs when trying to rewrite a term that appears " ++
          "as a dependent argument."
      let html ← renderUnfolds subExpr occ (← loc.location) props.replaceRange doc
      return html.getD
        <span>
          No unfolds found for {<InteractiveCode fmt={← ppExprTagged subExpr}/>}
        </span>

@[widget_module]
def UnfoldComponent : Component SelectInsertParams :=
  mk_rpc_widget% InteractiveUnfold.rpc

elab stx:"unfold?" : tactic => do

  let some range := (← getFileMap).rangeOfStx? stx | return

  Widget.savePanelWidgetInfo (hash UnfoldComponent.javascript)

    (pure <| json% { replaceRange : $range }) stx

syntax (name := unfoldCommand) "#unfold? " term : command

open Elab

@[command_elab unfoldCommand]
def elabUnfoldCommand : Command.CommandElab := fun stx =>
  withoutModifyingEnv <| Command.runTermElabM fun _ => Term.withDeclName `_unfold do
    let e ← Term.elabTerm stx[1] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)  let e ← instantiateMVars e
    let unfolds ← filteredUnfolds e
    if unfolds.isEmpty then
      logInfo m! "No unfolds found for {e}"
    else
      let unfolds := unfolds.toList.map (m! "· {·}")
      logInfo (m! "Unfolds for {e}:\n"
        ++ .joinSep unfolds "\n")

end InteractiveUnfold

end Mathlib.Tactic
