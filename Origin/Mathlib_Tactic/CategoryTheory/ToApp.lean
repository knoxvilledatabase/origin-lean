/-
Extracted from Tactic/CategoryTheory/ToApp.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Util.AddRelatedDecl

/-!
# The `to_app` attribute

Adding `@[to_app]` to a lemma named `F` of shape `∀ .., η = θ`, where `η θ : f ⟶ g` are 2-morphisms
in some bicategory, create a new lemma named `F_app`. This lemma is obtained by first specializing
the bicategory in which the equality is taking place to `Cat`, then applying `NatTrans.congr_app`
to obtain a proof of `∀ ... (X : Cat), η.app X = θ.app X`, and finally simplifying the conclusion
using some basic lemmas in the bicategory `Cat`:
`Cat.whiskerLeft_app`, `Cat.whiskerRight_app`, `Cat.id_app`, `Cat.comp_app` and `Cat.eqToHom_app`

So, for example, if the conclusion of `F` is `f ◁ η = θ` then the conclusion of `F_app` will be
`η.app (f.obj X) = θ.app X`.

This is useful for automatically generating lemmas that can be applied to expressions of 1-morphisms
in `Cat` which contain components of 2-morphisms.

There is also a term elaborator `to_app_of% t` for use within proofs.
-/

open Lean Meta Elab Tactic

open Mathlib.Tactic

namespace CategoryTheory

def catAppSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [
    ``Cat.whiskerLeft_app, ``Cat.whiskerRight_app, ``Cat.id_app, ``Cat.comp_app,
    ``Cat.eqToHom_app] e
    (config := { decide := false })

def toCatExpr (e : Expr) : MetaM Expr := do
  let (args, binderInfos, conclusion) ← forallMetaTelescope (← inferType e)
  -- Find the expression corresponding to the bicategory, by anylizing `η = θ` (i.e. conclusion)
  let B ←
    match conclusion.getAppFnArgs with
    | (`Eq, #[_, η, _]) =>
      match (← inferType η).getAppFnArgs with
      | (`Quiver.Hom, #[_, _, f, _]) =>
        match (← inferType f).getAppFnArgs with
        | (`Quiver.Hom, #[_, _, a, _]) => inferType a
        | _ => throwError "The conclusion {conclusion} is not an equality of 2-morphisms!"
      | _ => throwError "The conclusion {conclusion} is not an equality of 2-morphisms!"
    | _ => throwError "The conclusion {conclusion} is not an equality!"
  -- Create level metavariables to be used for `Cat.{v, u}`
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  -- Assign `B` to `Cat.{v, u}`
  let _ ← isDefEq B (.const ``Cat [v, u])
  -- Assign the right bicategory instance to `Cat.{v, u}`
  let some inst ← args.findM? fun x => do
      return (← inferType x).getAppFnArgs == (`CategoryTheory.Bicategory, #[B])
    | throwError "Can not find the argument for the bicategory instance of the bicategory in which \
      the equality is taking place."
  let _ ← isDefEq inst (.const ``CategoryTheory.Cat.bicategory [v, u])
  -- Construct the new expression
  let value := mkAppN e args
  let rec
  /-- Recursive function which applies `mkLambdaFVars` stepwise
  (so that each step can have different binderinfos) -/
    apprec (i : Nat) (e : Expr) : MetaM Expr := do
      if i < args.size then
        let arg := args[i]!
        let bi := binderInfos[i]!
        let e' ← apprec (i + 1) e
        unless arg != B && arg != inst do return e'
        mkLambdaFVars #[arg] e' (binderInfoForMVars := bi)
      else
        return e
  let value ← apprec 0 value
  return value

def toAppExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do simpType catAppSimp (← mkAppM ``NatTrans.congr_app #[e])) e

syntax (name := to_app) "to_app" (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {

  name := `to_app

  descr := ""

  applicationTime := .afterCompilation

  add := fun src ref kind => match ref with

  | `(attr| to_app $[(attr := $stx?,*)]?) => MetaM.run' do

    if (kind != AttributeKind.global) then

      throwError "`to_app` can only be used as a global attribute"

    addRelatedDecl src "_app" ref stx? fun type value levels => do

      let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar

      let value ← mkExpectedTypeHint value type

      let value := value.instantiateLevelParams levels levelMVars

      let newValue ← toAppExpr (← toCatExpr value)

      let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) newValue

      let output := (r.expr, r.newParamNames.toList)

      pure output

  | _ => throwUnsupportedSyntax }

open Term in

elab "to_app_of% " t:term : term => do

  toAppExpr (← elabTerm t none)

end CategoryTheory
