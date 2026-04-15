/-
Extracted from Tactic/CategoryTheory/Coherence.lean
Genuine: 11 of 25 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Lean.Meta
import Mathlib.Tactic.CategoryTheory.BicategoryCoherence
import Mathlib.Tactic.CategoryTheory.MonoidalComp

/-!
# A `coherence` tactic for monoidal categories

We provide a `coherence` tactic,
which proves equations where the two sides differ by replacing
strings of monoidal structural morphisms with other such strings.
(The replacements are always equalities by the monoidal coherence theorem.)

A simpler version of this tactic is `pure_coherence`,
which proves that any two morphisms (with the same source and target)
in a monoidal category which are built out of associators and unitors
are equal.

-/

universe v u

open CategoryTheory FreeMonoidalCategory

namespace Mathlib.Tactic.Coherence

variable {C : Type u} [Category.{v} C]

open scoped MonoidalCategory

noncomputable section lifting

variable [MonoidalCategory C]

class LiftObj (X : C) where
  protected lift : FreeMonoidalCategory C

instance LiftObj_unit : LiftObj (𝟙_ C) := ⟨unit⟩

instance LiftObj_tensor (X Y : C) [LiftObj X] [LiftObj Y] : LiftObj (X ⊗ Y) where
  lift := LiftObj.lift X ⊗ LiftObj.lift Y

instance (priority := 100) LiftObj_of (X : C) : LiftObj X := ⟨of X⟩

class LiftHom {X Y : C} [LiftObj X] [LiftObj Y] (f : X ⟶ Y) where
  protected lift : LiftObj.lift X ⟶ LiftObj.lift Y

instance LiftHom_id (X : C) [LiftObj X] : LiftHom (𝟙 X) := ⟨𝟙 _⟩

instance LiftHom_left_unitor_hom (X : C) [LiftObj X] : LiftHom (λ_ X).hom where
  lift := (λ_ (LiftObj.lift X)).hom

instance LiftHom_left_unitor_inv (X : C) [LiftObj X] : LiftHom (λ_ X).inv where
  lift := (λ_ (LiftObj.lift X)).inv

instance LiftHom_right_unitor_hom (X : C) [LiftObj X] : LiftHom (ρ_ X).hom where
  lift := (ρ_ (LiftObj.lift X)).hom

instance LiftHom_right_unitor_inv (X : C) [LiftObj X] : LiftHom (ρ_ X).inv where
  lift := (ρ_ (LiftObj.lift X)).inv

instance LiftHom_associator_hom (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).hom where
  lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).hom

instance LiftHom_associator_inv (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).inv where
  lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).inv

instance LiftHom_comp {X Y Z : C} [LiftObj X] [LiftObj Y] [LiftObj Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [LiftHom f] [LiftHom g] : LiftHom (f ≫ g) where
  lift := LiftHom.lift f ≫ LiftHom.lift g

instance liftHom_WhiskerLeft (X : C) [LiftObj X] {Y Z : C} [LiftObj Y] [LiftObj Z]
    (f : Y ⟶ Z) [LiftHom f] : LiftHom (X ◁ f) where
  lift := LiftObj.lift X ◁ LiftHom.lift f

instance liftHom_WhiskerRight {X Y : C} (f : X ⟶ Y) [LiftObj X] [LiftObj Y] [LiftHom f]
    {Z : C} [LiftObj Z] : LiftHom (f ▷ Z) where
  lift := LiftHom.lift f ▷ LiftObj.lift Z

instance LiftHom_tensor {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z]
    (f : W ⟶ X) (g : Y ⟶ Z) [LiftHom f] [LiftHom g] : LiftHom (f ⊗ g) where
  lift := LiftHom.lift f ⊗ LiftHom.lift g

end lifting

open Lean Meta Elab Tactic

def exception {α : Type} (g : MVarId) (msg : MessageData) : MetaM α :=
  throwTacticEx `monoidal_coherence g msg

def exception' (msg : MessageData) : TacticM Unit := do
  try
    liftMetaTactic (exception (msg := msg))
  catch _ =>
    -- There might not be any goals
    throwError msg

def mkProjectMapExpr (e : Expr) : TermElabM Expr := do
  Term.elabTerm
    (← ``(FreeMonoidalCategory.projectMap _root_.id _ _ (LiftHom.lift $(← Term.exprToSyntax e))))
    none

def monoidal_coherence (g : MVarId) : TermElabM Unit := g.withContext do
  withOptions (fun opts => synthInstance.maxSize.set opts
    (max 512 (synthInstance.maxSize.get opts))) do
  let thms := [``MonoidalCoherence.iso, ``Iso.trans, ``Iso.symm, ``Iso.refl,
    ``MonoidalCategory.whiskerRightIso, ``MonoidalCategory.whiskerLeftIso].foldl
    (·.addDeclToUnfoldCore ·) {}
  let (ty, _) ← dsimp (← g.getType) { simpTheorems := #[thms] }
  let some (_, lhs, rhs) := (← whnfR ty).eq? | exception g "Not an equation of morphisms."
  let projectMap_lhs ← mkProjectMapExpr lhs
  let projectMap_rhs ← mkProjectMapExpr rhs
  -- This new equation is defeq to the original by assumption
  -- on the `LiftObj` and `LiftHom` instances.
  let g₁ ← g.change (← mkEq projectMap_lhs projectMap_rhs)
  let [g₂] ← g₁.applyConst ``congrArg
    | exception g "congrArg failed in coherence"
  let [] ← g₂.applyConst ``Subsingleton.elim
    | exception g "This shouldn't happen; Subsingleton.elim does not create goals."

elab "monoidal_coherence" : tactic => do monoidal_coherence (← getMainGoal)

open Mathlib.Tactic.BicategoryCoherence

elab (name := pure_coherence) "pure_coherence" : tactic => do

  let g ← getMainGoal

  monoidal_coherence g <|> bicategory_coherence g

@[nolint unusedArguments]
lemma assoc_liftHom {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y]
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) [LiftHom f] [LiftHom g] :
    f ≫ (g ≫ h) = (f ≫ g) ≫ h :=
  (Category.assoc _ _ _).symm

elab (name := liftable_prefixes) "liftable_prefixes" : tactic => do

  withOptions (fun opts => synthInstance.maxSize.set opts

    (max 256 (synthInstance.maxSize.get opts))) do

  evalTactic (← `(tactic|

    (simp (config := {failIfUnchanged := false}) only

      [monoidalComp, bicategoricalComp, Category.assoc, BicategoricalCoherence.iso,

      MonoidalCoherence.iso, Iso.trans, Iso.symm, Iso.refl,

      MonoidalCategory.whiskerRightIso, MonoidalCategory.whiskerLeftIso,

      Bicategory.whiskerRightIso, Bicategory.whiskerLeftIso]) <;>

    (apply (cancel_epi (𝟙 _)).1 <;> try infer_instance) <;>

    (simp (config := {failIfUnchanged := false}) only

      [assoc_liftHom, Mathlib.Tactic.BicategoryCoherence.assoc_liftHom₂])))

lemma insert_id_lhs {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y) (w : f ≫ 𝟙 _ = g) :
    f = g := by
  simpa using w

lemma insert_id_rhs {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y) (w : f = g ≫ 𝟙 _) :
    f = g := by
  simpa using w

def insertTrailingIds (g : MVarId) : MetaM MVarId := do
  let some (_, lhs, rhs) := (← withReducible g.getType').eq? | exception g "Not an equality."
  let mut g := g
  if !(lhs.isAppOf ``CategoryStruct.comp) then
    let [g'] ← g.applyConst ``insert_id_lhs | exception g "failed to apply insert_id_lhs"
    g := g'
  if !(rhs.isAppOf ``CategoryStruct.comp) then
    let [g'] ← g.applyConst ``insert_id_rhs | exception g "failed to apply insert_id_rhs"
    g := g'
  return g

def coherence_loop (maxSteps := 37) : TacticM Unit :=
  match maxSteps with
  | 0 => exception' "`coherence` tactic reached iteration limit"
  | maxSteps' + 1 => do
    -- To prove an equality `f = g` in a monoidal category,
    -- first try the `pure_coherence` tactic on the entire equation:
    evalTactic (← `(tactic| pure_coherence)) <|> do
    -- Otherwise, rearrange so we have a maximal prefix of each side
    -- that is built out of unitors and associators:
    evalTactic (← `(tactic| liftable_prefixes)) <|>
      exception' "Something went wrong in the `coherence` tactic: \
        is the target an equation in a monoidal category?"
    -- The goal should now look like `f₀ ≫ f₁ = g₀ ≫ g₁`,
    liftMetaTactic MVarId.congrCore
    -- and now we have two goals `f₀ = g₀` and `f₁ = g₁`.
    -- Discharge the first using `coherence`,
    evalTactic (← `(tactic| { pure_coherence })) <|>
      exception' "`coherence` tactic failed, subgoal not true in the free monoidal category"
    -- Then check that either `g₀` is identically `g₁`,
    evalTactic (← `(tactic| rfl)) <|> do
      -- or that both are compositions,
      liftMetaTactic' insertTrailingIds
      liftMetaTactic MVarId.congrCore
      -- with identical first terms,
      evalTactic (← `(tactic| rfl)) <|>
        exception' "`coherence` tactic failed, non-structural morphisms don't match"
      -- and whose second terms can be identified by recursively called `coherence`.
      coherence_loop maxSteps'

open Lean.Parser.Tactic

syntax (name := monoidal_simps) "monoidal_simps" optConfig : tactic

elab_rules : tactic

| `(tactic| monoidal_simps $cfg:optConfig) => do

  evalTactic (← `(tactic|

    simp $cfg only [

      Category.assoc, MonoidalCategory.tensor_whiskerLeft, MonoidalCategory.id_whiskerLeft,

      MonoidalCategory.whiskerRight_tensor, MonoidalCategory.whiskerRight_id,

      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_id,

      MonoidalCategory.comp_whiskerRight, MonoidalCategory.id_whiskerRight,

      MonoidalCategory.whisker_assoc,

      MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id];

    try simp only [MonoidalCategory.tensorHom_def]

    ))

syntax (name := coherence) "coherence" : tactic

elab_rules : tactic

| `(tactic| coherence) => do

  evalTactic (← `(tactic|

    (simp (config := {failIfUnchanged := false}) only [bicategoricalComp, monoidalComp]);

    whisker_simps (config := {failIfUnchanged := false});

    monoidal_simps (config := {failIfUnchanged := false})))

  coherence_loop

end Coherence

end Mathlib.Tactic
