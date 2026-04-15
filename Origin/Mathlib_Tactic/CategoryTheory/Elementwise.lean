/-
Extracted from Tactic/CategoryTheory/Elementwise.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Util.AddRelatedDecl
import Batteries.Tactic.Lint

/-!
# Tools to reformulate category-theoretic lemmas in concrete categories

## The `elementwise` attribute

The `elementwise` attribute generates lemmas for concrete categories from lemmas
that equate morphisms in a category.

A sort of inverse to this for the `Type*` category is the `@[higher_order]` attribute.

For more details, see the documentation attached to the `syntax` declaration.

## Main definitions

- The `@[elementwise]` attribute.

- The ``elementwise_of% h` term elaborator.

## Implementation

This closely follows the implementation of the `@[reassoc]` attribute, due to Simon Hudon and
reimplemented by Kim Morrison in Lean 4.
-/

open Lean Meta Elab Tactic

open Mathlib.Tactic

namespace Tactic.Elementwise

open CategoryTheory

section theorems

universe u

theorem forall_congr_forget_Type (α : Type u) (p : α → Prop) :
    (∀ (x : (forget (Type u)).obj α), p x) ↔ ∀ (x : α), p x := Iff.rfl

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

theorem forget_hom_Type (α β : Type u) (f : α ⟶ β) : DFunLike.coe f = f := rfl

theorem hom_elementwise {C : Type*} [Category C] [ConcreteCategory C]
    {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x := by rw [h]

end theorems

def elementwiseThms : List Name :=
  [``CategoryTheory.coe_id, ``CategoryTheory.coe_comp, ``CategoryTheory.comp_apply,
    ``CategoryTheory.id_apply,
    -- further simplifications if the category is `Type`
    ``forget_hom_Type, ``forall_congr_forget_Type,
    -- simp can itself simplify trivial equalities into `true`. Adding this lemma makes it
    -- easier to detect when this has occurred.
    ``implies_true]

def elementwiseExpr (src : Name) (type pf : Expr) (simpSides := true) :
    MetaM (Expr × Option Level) := do
  let type := (← instantiateMVars type).cleanupAnnotations
  forallTelescope type fun fvars type' => do
    mkHomElementwise type' (← mkExpectedTypeHint (mkAppN pf fvars) type') fun eqPf instConcr? => do
      -- First simplify using elementwise-specific lemmas
      let mut eqPf' ← simpType (simpOnlyNames elementwiseThms (config := { decide := false })) eqPf
      if (← inferType eqPf') == .const ``True [] then
        throwError "elementwise lemma for {src} is trivial after applying ConcreteCategory \
          lemmas, which can be caused by how applications are unfolded. \
          Using elementwise is unnecessary."
      if simpSides then
        let ctx := { ← Simp.Context.mkDefault with config.decide := false }
        let (ty', eqPf'') ← simpEq (fun e => return (← simp e ctx).1) (← inferType eqPf') eqPf'
        -- check that it's not a simp-trivial equality:
        forallTelescope ty' fun _ ty' => do
          if let some (_, lhs, rhs) := ty'.eq? then
            if ← Batteries.Tactic.Lint.isSimpEq lhs rhs then
              throwError "applying simp to both sides reduces elementwise lemma for {src} \
                to the trivial equality {ty'}. \
                Either add `nosimp` or remove the `elementwise` attribute."
        eqPf' ← mkExpectedTypeHint eqPf'' ty'
      if let some (w, instConcr) := instConcr? then
        return (← Meta.mkLambdaFVars (fvars.push instConcr) eqPf', w)
      else
        return (← Meta.mkLambdaFVars fvars eqPf', none)
where
  /-- Given an equality, extract a `Category` instance from it or raise an error.
  Returns the name of the category and its instance. -/
  extractCatInstance (eqTy : Expr) : MetaM (Expr × Expr) := do
    let some (α, _, _) := eqTy.cleanupAnnotations.eq? | failure
    let (``Quiver.Hom, #[_, instQuiv, _, _]) := α.getAppFnArgs | failure
    let (``CategoryTheory.CategoryStruct.toQuiver, #[_, instCS]) := instQuiv.getAppFnArgs | failure
    let (``CategoryTheory.Category.toCategoryStruct, #[C, instC]) := instCS.getAppFnArgs | failure
    return (C, instC)
  mkHomElementwise {α} (eqTy eqPf : Expr) (k : Expr → Option (Level × Expr) → MetaM α) :
      MetaM α := do
    let (C, instC) ← try extractCatInstance eqTy catch _ =>
      throwError "elementwise expects equality of morphisms in a category"
    -- First try being optimistic that there is already a ConcreteCategory instance.
    if let some eqPf' ← observing? (mkAppM ``hom_elementwise #[eqPf]) then
      k eqPf' none
    else
      -- That failed, so we need to introduce the instance, which takes creating
      -- a fresh universe level for `ConcreteCategory`'s forgetful functor.
      let .app (.const ``Category [v, u]) _ ← inferType instC
        | throwError "internal error in elementwise"
      let w ← mkFreshLevelMVar
      let cty : Expr := mkApp2 (.const ``ConcreteCategory [w, v, u]) C instC
      withLocalDecl `inst .instImplicit cty fun cfvar => do
        let eqPf' ← mkAppM ``hom_elementwise #[eqPf]
        k eqPf' (some (w, cfvar))

private partial def mkUnusedName (names : List Name) (baseName : Name) : Name :=
  if not (names.contains baseName) then
    baseName
  else
    let rec loop (i : Nat := 0) : Name :=
      let w := Name.appendIndexAfter baseName i
      if names.contains w then
        loop (i + 1)
      else
        w
    loop 1

syntax (name := elementwise) "elementwise"

  " nosimp"? (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {

  name := `elementwise

  descr := ""

  applicationTime := .afterCompilation

  add := fun src ref kind => match ref with

  | `(attr| elementwise $[nosimp%$nosimp?]? $[(attr := $stx?,*)]?) => MetaM.run' do

    if (kind != AttributeKind.global) then

      throwError "`elementwise` can only be used as a global attribute"

    addRelatedDecl src "_apply" ref stx? fun type value levels => do

      let (newValue, level?) ← elementwiseExpr src type value (simpSides := nosimp?.isNone)

      let newLevels ← if let some level := level? then do

        let w := mkUnusedName levels `w

        unless ← isLevelDefEq level (mkLevelParam w) do

          throwError "Could not create level parameter for ConcreteCategory instance"

        pure <| w :: levels

      else

        pure levels

      pure (newValue, newLevels)

  | _ => throwUnsupportedSyntax }

elab "elementwise_of% " t:term : term => do

  let e ← Term.elabTerm t none

  let (pf, _) ← elementwiseExpr .anonymous (← inferType e) e (simpSides := false)

  return pf

syntax "elementwise" (ppSpace colGt ident)* : tactic

syntax "elementwise!" (ppSpace colGt ident)* : tactic

end Tactic.Elementwise
