/-
Extracted from Tactic/CategoryTheory/Reassoc.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Util.AddRelatedDecl

noncomputable section

/-!
# The `reassoc` attribute

Adding `@[reassoc]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : X ⟶ Y` in some category
will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h`
but with the conclusions simplified using the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).

This is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.

There is also a term elaborator `reassoc_of% t` for use within proofs.
-/

open Lean Meta Elab Tactic

open Mathlib.Tactic

namespace CategoryTheory

variable {C : Type*} [Category C]

theorem eq_whisker' {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) :
    f ≫ h = g ≫ h := by rw [w]

def categorySimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Category.comp_id, ``Category.id_comp, ``Category.assoc,
    ``Functor.id_obj, ``Functor.id_map, ``Functor.comp_obj, ``Functor.comp_map] e
    (config := { decide := false })

def reassocExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do simpType categorySimp (← mkAppM ``eq_whisker' #[e])) e

syntax (name := reassoc) "reassoc" (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {

  name := `reassoc

  descr := ""

  applicationTime := .afterCompilation

  add := fun src ref kind => match ref with

  | `(attr| reassoc $[(attr := $stx?,*)]?) => MetaM.run' do

    if (kind != AttributeKind.global) then

      throwError "`reassoc` can only be used as a global attribute"

    addRelatedDecl src "_assoc" ref stx? fun type value levels => do

      pure (← reassocExpr (← mkExpectedTypeHint value type), levels)

  | _ => throwUnsupportedSyntax }

open Term in

elab "reassoc_of% " t:term : term => do
  reassocExpr (← elabTerm t none)

end CategoryTheory
