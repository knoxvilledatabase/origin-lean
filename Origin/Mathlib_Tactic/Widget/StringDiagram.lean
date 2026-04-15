/-
Extracted from Tactic/Widget/StringDiagram.lean
Genuine: 38 of 39 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Presentation.Expr
import ProofWidgets.Component.HtmlDisplay
import Mathlib.Tactic.CategoryTheory.Bicategory.Normalize
import Mathlib.Tactic.CategoryTheory.Monoidal.Normalize

/-!
# String Diagram Widget

This file provides meta infrastructure for displaying string diagrams for morphisms in monoidal
categories in the infoview. To enable the string diagram widget, you need to import this file and
inserting `with_panel_widgets [Mathlib.Tactic.Widget.StringDiagram]` at the beginning of the
proof. Alternatively, you can also write
```lean
open Mathlib.Tactic.Widget
show_panel_widgets [local StringDiagram]
```
to enable the string diagram widget in the current section.

We also have the `#string_diagram` command. For example,
```lean
#string_diagram MonoidalCategory.whisker_exchange
```
displays the string diagram for the exchange law of the left and right whiskerings.

String diagrams are graphical representations of morphisms in monoidal categories, which are
useful for rewriting computations. More precisely, objects in a monoidal category is represented
by strings, and morphisms between two objects is represented by nodes connecting two strings
associated with the objects. The tensor product `X ⊗ Y` corresponds to putting strings associated
with `X` and `Y` horizontally (from left to right), and the composition of morphisms `f : X ⟶ Y`
and `g : Y ⟶ Z` corresponds to connecting two nodes associated with `f` and `g` vertically (from
top to bottom) by strings associated with `Y`.

Currently, the string diagram widget provided in this file deals with equalities of morphisms
in monoidal categories. It displays string diagrams corresponding to the morphisms for the
left-hand and right-hand sides of the equality.

Some examples can be found in `test/StringDiagram.lean`.

When drawing string diagrams, it is common to ignore associators and unitors. We follow this
convention. To do this, we need to extract non-structural morphisms that are not associators
and unitors from lean expressions. This operation is performed using the `Tactic.Monoidal.eval`
function.

A monoidal category can be viewed as a bicategory with a single object. The program in this
file can also be used to display the string diagram for general bicategories (see the wip
PR https://github.com/leanprover-community/mathlib4/pull/12107). With this in mind we will sometimes refer to objects and morphisms in monoidal
categories as 1-morphisms and 2-morphisms respectively, borrowing the terminology of bicategories.
Note that the relation between monoidal categories and bicategories is formalized in
`Mathlib.CategoryTheory.Bicategory.SingleObj`, although the string diagram widget does not use
it directly.

-/

namespace Mathlib.Tactic

open Lean Meta Elab

open CategoryTheory

open BicategoryLike

namespace Widget.StringDiagram

initialize registerTraceClass `string_diagram

/-! ## Objects in string diagrams -/

structure AtomNode : Type where
  /-- The vertical position of the node in the string diagram. -/
  vPos : ℕ
  /-- The horizontal position of the node in the string diagram, counting strings in domains. -/
  hPosSrc : ℕ
  /-- The horizontal position of the node in the string diagram, counting strings in codomains. -/
  hPosTar : ℕ
  /-- The underlying expression of the node. -/
  atom : Atom

structure IdNode : Type where
  /-- The vertical position of the node in the string diagram. -/
  vPos : ℕ
  /-- The horizontal position of the node in the string diagram, counting strings in domains. -/
  hPosSrc : ℕ
  /-- The horizontal position of the node in the string diagram, counting strings in codomains. -/
  hPosTar : ℕ
  /-- The underlying expression of the node. -/
  id : Atom₁

inductive Node : Type
  | atom : AtomNode → Node
  | id : IdNode → Node

def Node.e : Node → Expr
  | Node.atom n => n.atom.e
  | Node.id n => n.id.e

def Node.srcList : Node → List (Node × Atom₁)
  | Node.atom n => n.atom.src.toList.map (fun f ↦ (.atom n, f))
  | Node.id n => [(.id n, n.id)]

def Node.tarList : Node → List (Node × Atom₁)
  | Node.atom n => n.atom.tgt.toList.map (fun f ↦ (.atom n, f))
  | Node.id n => [(.id n, n.id)]

def Node.vPos : Node → ℕ
  | Node.atom n => n.vPos
  | Node.id n => n.vPos

def Node.hPosSrc : Node → ℕ
  | Node.atom n => n.hPosSrc
  | Node.id n => n.hPosSrc

def Node.hPosTar : Node → ℕ
  | Node.atom n => n.hPosTar
  | Node.id n => n.hPosTar

structure Strand : Type where
  /-- The horizontal position of the strand in the string diagram. -/
  hPos : ℕ
  /-- The start point of the strand in the string diagram. -/
  startPoint : Node
  /-- The end point of the strand in the string diagram. -/
  endPoint : Node
  /-- The underlying expression of the strand. -/
  atom₁ : Atom₁

def Strand.vPos (s : Strand) : ℕ :=
  s.startPoint.vPos

end Widget.StringDiagram

namespace BicategoryLike

open Widget.StringDiagram

def WhiskerRight.nodes (v h₁ h₂ : ℕ) : WhiskerRight → List Node
  | WhiskerRight.of η => [.atom ⟨v, h₁, h₂, η⟩]
  | WhiskerRight.whisker _ η f =>
    let ηs := η.nodes v h₁ h₂
    let k₁ := (ηs.map (fun n ↦ n.srcList)).flatten.length
    let k₂ := (ηs.map (fun n ↦ n.tarList)).flatten.length
    let s : Node := .id ⟨v, h₁ + k₁, h₂ + k₂, f⟩
    ηs ++ [s]

def HorizontalComp.nodes (v h₁ h₂ : ℕ) : HorizontalComp → List Node
  | HorizontalComp.of η => η.nodes v h₁ h₂
  | HorizontalComp.cons _ η ηs =>
    let s₁ := η.nodes v h₁ h₂
    let k₁ := (s₁.map (fun n ↦ n.srcList)).flatten.length
    let k₂ := (s₁.map (fun n ↦ n.tarList)).flatten.length
    let s₂ := ηs.nodes v (h₁ + k₁) (h₂ + k₂)
    s₁ ++ s₂

def WhiskerLeft.nodes (v h₁ h₂ : ℕ) : WhiskerLeft → List Node
  | WhiskerLeft.of η => η.nodes v h₁ h₂
  | WhiskerLeft.whisker _ f η =>
    let s : Node := .id ⟨v, h₁, h₂, f⟩
    let ss := η.nodes v (h₁ + 1) (h₂ + 1)
    s :: ss

variable {ρ : Type} [MonadMor₁ (CoherenceM ρ)]

def topNodes (η : WhiskerLeft) : CoherenceM ρ (List Node) := do
  return (← η.srcM).toList.enum.map (fun (i, f) => .id ⟨0, i, i, f⟩)

def NormalExpr.nodesAux (v : ℕ) : NormalExpr → CoherenceM ρ (List (List Node))
  | NormalExpr.nil _ α => return [(← α.srcM).toList.enum.map (fun (i, f) => .id ⟨v, i, i, f⟩)]
  | NormalExpr.cons _ _ η ηs => do
    let s₁ := η.nodes v 0 0
    let s₂ ← ηs.nodesAux (v + 1)
    return s₁ :: s₂

def NormalExpr.nodes (e : NormalExpr) : CoherenceM ρ (List (List Node)) :=
  match e with
  | NormalExpr.nil _ _ => return []
  | NormalExpr.cons _ _ η _ => return (← topNodes η) :: (← e.nodesAux 1)

def pairs {α : Type} : List α → List (α × α) :=
  fun l => l.zip (l.drop 1)

def NormalExpr.strands (e : NormalExpr) : CoherenceM ρ (List (List Strand)) := do
  let l ← e.nodes
  (pairs l).mapM fun (x, y) ↦ do
    let xs := (x.map (fun n ↦ n.tarList)).flatten
    let ys := (y.map (fun n ↦ n.srcList)).flatten
    -- sanity check
    if xs.length ≠ ys.length then
      throwError "The number of the start and end points of a string does not match."
    (xs.zip ys).enum.mapM fun (k, (n₁, f₁), (n₂, _)) => do
      return ⟨n₁.hPosTar + k, n₁, n₂, f₁⟩

end BicategoryLike

namespace Widget.StringDiagram

structure PenroseVar : Type where
  /-- The identifier of the variable. -/
  ident : String
  /-- The indices of the variable. -/
  indices : List ℕ
  /-- The underlying expression of the variable. -/
  e : Expr

instance : ToString PenroseVar :=
  ⟨fun v => v.ident ++ v.indices.foldl (fun s x => s ++ s!"_{x}") ""⟩

def Node.toPenroseVar (n : Node) : PenroseVar :=
  ⟨"E", [n.vPos, n.hPosSrc, n.hPosTar], n.e⟩

def Strand.toPenroseVar (s : Strand) : PenroseVar :=
  ⟨"f", [s.vPos, s.hPos], s.atom₁.e⟩

/-! ## Widget for general string diagrams -/

open ProofWidgets Penrose DiagramBuilderM Lean.Server

open scoped Jsx in

def addPenroseVar (tp : String) (v : PenroseVar) :
    DiagramBuilderM Unit := do
  let h := <InteractiveCode fmt={← Widget.ppExprTagged v.e} />
  addEmbed (toString v) tp h

def addConstructor (tp : String) (v : PenroseVar) (nm : String) (vs : List PenroseVar) :
    DiagramBuilderM Unit := do
  let vs' := ", ".intercalate (vs.map (fun v => toString v))
  addInstruction s!"{tp} {v} := {nm} ({vs'})"

open scoped Jsx in

def mkStringDiagram (nodes : List (List Node)) (strands : List (List Strand)) :
    DiagramBuilderM PUnit := do
  /- Add 2-morphisms. -/
  for x in nodes.flatten do
    match x with
    | .atom _ => do addPenroseVar "Atom" x.toPenroseVar
    | .id _ => do addPenroseVar "Id" x.toPenroseVar
  /- Add constraints. -/
  for l in nodes do
    for (x₁, x₂) in pairs l do
      addInstruction s!"Left({x₁.toPenroseVar}, {x₂.toPenroseVar})"
  /- Add constraints. -/
  for (l₁, l₂) in pairs nodes do
    if let .some x₁ := l₁.head? then
      if let .some x₂ := l₂.head? then
        addInstruction s!"Above({x₁.toPenroseVar}, {x₂.toPenroseVar})"
  /- Add 1-morphisms as strings. -/
  for l in strands do
    for s in l do
      addConstructor "Mor1" s.toPenroseVar
        "MakeString" [s.startPoint.toPenroseVar, s.endPoint.toPenroseVar]

def dsl :=
  include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.dsl"

def sty :=
  include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.sty"

inductive Kind where
  | monoidal : Kind
  | bicategory : Kind
  | none : Kind

def Kind.name : Kind → Name
  | Kind.monoidal => `monoidal
  | Kind.bicategory => `bicategory
  | Kind.none => default

def mkKind (e : Expr) : MetaM Kind := do
  let e ← instantiateMVars e
  let e ← (match (← whnfR e).eq? with
    | some (_, lhs, _) => return lhs
    | none => return e)
  let ctx? ← BicategoryLike.mkContext? (ρ := Bicategory.Context) e
  match ctx? with
  | .some _ => return .bicategory
  | .none =>
    let ctx? ← BicategoryLike.mkContext? (ρ := Monoidal.Context) e
    match ctx? with
    | .some _ => return .monoidal
    | .none => return .none

open scoped Jsx in

def stringM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let k ← mkKind e
  let x : Option (List (List Node) × List (List Strand)) ← (match k with
    | .monoidal => do
      let .some ctx ← BicategoryLike.mkContext? (ρ := Monoidal.Context) e | return .none
      CoherenceM.run (ctx := ctx) do
        let e' := (← BicategoryLike.eval k.name (← MkMor₂.ofExpr e)).expr
        return .some (← e'.nodes, ← e'.strands)
    | .bicategory => do
      let .some ctx ← BicategoryLike.mkContext? (ρ := Bicategory.Context) e | return .none
      CoherenceM.run (ctx := ctx) do
        let e' := (← BicategoryLike.eval k.name (← MkMor₂.ofExpr e)).expr
        return .some (← e'.nodes, ← e'.strands)
    | .none => return .none)
  match x with
  | .none => return none
  | .some (nodes, strands) => do
    DiagramBuilderM.run do
      mkStringDiagram nodes strands
      trace[string_diagram] "Penrose substance: \n{(← get).sub}"
      match ← DiagramBuilderM.buildDiagram dsl sty with
      | some html => return html
      | none => return <span>No non-structural morphisms found.</span>

open scoped Jsx in

def mkEqHtml (lhs rhs : Html) : Html :=
  <div className="flex">
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">String diagram for LHS</summary> {lhs}
      </details>
    </div>
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">String diagram for RHS</summary> {rhs}
      </details>
    </div>
  </div>

def stringEqM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  let some lhs ← stringM? lhs | return none
  let some rhs ← stringM? rhs | return none
  return some <| mkEqHtml lhs rhs

def stringMorOrEqM? (e : Expr) : MetaM (Option Html) := do
  forallTelescopeReducing (← inferType e) fun xs a => do
    if let some html ← stringM? (mkAppN e xs) then
      return some html
    else if let some html ← stringEqM? a then
      return some html
    else
      return none

@[expr_presenter]
def stringPresenter : ExprPresenter where
  userName := "String diagram"
  layoutKind := .block
  present type := do
    if let some html ← stringMorOrEqM? type then
      return html
    throwError "Couldn't find a 2-morphism to display a string diagram."

open scoped Jsx in

@[server_rpc_method]
def rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let html : Option Html ← (do
      if props.goals.isEmpty then
        return none
      let some g := props.goals[0]? | unreachable!
      g.ctx.val.runMetaM {} do
        g.mvarId.withContext do
          let type ← g.mvarId.getType
          stringEqM? type)
    match html with
    | none => return <span>No String Diagram.</span>
    | some inner => return inner

end StringDiagram

open ProofWidgets

@[widget_module]
def StringDiagram : Component PanelWidgetProps :=
  mk_rpc_widget% StringDiagram.rpc

open Command

#string_diagram MonoidalCategory.whisker_exchange

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {X Y : C} (f : 𝟙_ C ⟶ X ⊗ Y) in

#string_diagram f

```

-/

syntax (name := stringDiagram) "#string_diagram " term : command

@[command_elab stringDiagram, inherit_doc stringDiagram]
def elabStringDiagramCmd : CommandElab := fun
  | stx@`(#string_diagram $t:term) => do
    let html ← runTermElabM fun _ => do
      let e ← try mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverloadWithInfo t)
        catch _ => Term.levelMVarToParam (← instantiateMVars (← Term.elabTerm t none))
      match ← StringDiagram.stringMorOrEqM? e with
      | .some html => return html
      | .none => throwError "could not find a morphism or equality: {e}"
    liftCoreM <| Widget.savePanelWidgetInfo
      (hash HtmlDisplay.javascript)
      (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
      stx
  | stx => throwError "Unexpected syntax {stx}."

end Mathlib.Tactic.Widget
