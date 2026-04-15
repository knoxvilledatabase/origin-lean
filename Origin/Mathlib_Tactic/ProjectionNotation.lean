/-
Extracted from Tactic/ProjectionNotation.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Elab.AuxDef
import Mathlib.Init

/-!
# Pretty printing projection notation

**Deprecated** as of 2024-05-02 with Lean v4.8.0 since dot notation is now default with
the introduction of `pp.fieldNotation.generalized`, which handles dot notation pervasively
and correctly.


This module contains the `@[pp_dot]` attribute, which is used to configure functions to pretty print
using projection notation (i.e., like `x.f y` rather than `C.f x y`).

Core's projection delaborator collapses chains of ancestor projections.
For example, to turn `x.toFoo.toBar` into `x.toBar`.
The `pp_dot` attribute works together with this delaborator to completely collapse such chains.
-/

namespace Mathlib.ProjectionNotation

open Lean Parser Elab Term

open PrettyPrinter.Delaborator SubExpr

open Lean.Elab.Command

def mkExtendedFieldNotationUnexpander (f : Name) : CommandElabM Unit := do
  let .str A projName := f | throwError "Projection name must end in a string component."
  if let some _ := getStructureInfo? (← getEnv) A then
    -- If this is for a structure, then generate an extra `.toA` remover.
    -- It's easier to handle the two cases completely separately than to try to merge them.
    let .str _ A' := A | throwError "{A} must end in a string component"
    let toA : Name := .str .anonymous ("to" ++ A')
    elabCommand <| ← `(command|
      @[app_unexpander $(mkIdent f)]
      aux_def $(mkIdent <| Name.str f "unexpander") : Lean.PrettyPrinter.Unexpander := fun
        -- Having a zero-argument pattern prevents unnecessary parenthesization in output
        | `($$_ $$(x).$(mkIdent toA))
        | `($$_ $$x) => set_option hygiene false in `($$(x).$(mkIdent (.mkSimple projName)))
        | _ => throw ())
  else
    elabCommand <| ← `(command|
      @[app_unexpander $(mkIdent f)]
      aux_def $(mkIdent <| Name.str f "unexpander") : Lean.PrettyPrinter.Unexpander := fun
        -- Having this zero-argument pattern prevents unnecessary parenthesization in output
        | `($$_ $$x) => set_option hygiene false in `($$(x).$(mkIdent (.mkSimple projName)))
        | _ => throw ())

syntax (name := ppDotAttr) "pp_dot" : attr

initialize registerBuiltinAttribute {

  name := `ppDotAttr

  descr := ""

  applicationTime := .afterCompilation

  add := fun src ref kind => match ref with

  | `(attr| pp_dot) => do

    logWarning "\

      The @[pp_dot] attribute is deprecated now that dot notation is the default \

      with the introduction of `pp.fieldNotation.generalized` in Lean v4.8.0."

    if (kind != AttributeKind.global) then

      throwError "`pp_dot` can only be used as a global attribute"

    liftCommandElabM <| withRef ref <| mkExtendedFieldNotationUnexpander src

  | _ => throwUnsupportedSyntax }

end Mathlib.ProjectionNotation
