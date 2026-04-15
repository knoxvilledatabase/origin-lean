/-
Extracted from Tactic/PPWithUniv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init

/-!
# Attribute to pretty-print universe level parameters by default

This module contains the `pp_with_univ` attribute, which enables pretty-printing
of universe parameters for the associated declaration.  This is helpful for definitions like
`Ordinal`, where the universe levels are both relevant and not deducible from the arguments.
-/

namespace Mathlib.PPWithUniv

open Lean Parser PrettyPrinter Delaborator SubExpr Elab Command

def delabWithUniv : Delab :=
  whenPPOption (·.get pp.universes.name true) <|
  let enablePPUnivOnHead subExpr :=
    let expr := subExpr.expr
    let expr := mkAppN (expr.getAppFn.setOption pp.universes.name true) expr.getAppArgs
    { subExpr with expr }
  withTheReader SubExpr enablePPUnivOnHead delabApp

syntax (name := ppWithUnivAttr) "pp_with_univ" : attr

initialize registerBuiltinAttribute {

  name := `ppWithUnivAttr

  descr := ""

  applicationTime := .afterCompilation

  add := fun src ref kind => match ref with

  | `(attr| pp_with_univ) => do

    liftCommandElabM <| withRef ref do

      let attr ← Elab.elabAttr <| ← `(Term.attrInstance| delab $(mkIdent <| `app ++ src))

      liftTermElabM <| Term.applyAttributes ``delabWithUniv #[{attr with kind}]

  | _ => throwUnsupportedSyntax }

end PPWithUniv

end Mathlib
