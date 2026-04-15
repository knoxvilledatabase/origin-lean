/-
Extracted from Tactic/Lift.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.Tactic.Basic
import Batteries.Lean.Expr
import Batteries.Lean.Meta.UnusedNames

/-!
# lift tactic

This file defines the `lift` tactic, allowing the user to lift elements from one type to another
under a specified condition.

## Tags

lift, tactic
-/

class CanLift (α β : Sort*) (coe : outParam <| β → α) (cond : outParam <| α → Prop) : Prop where
  /-- An element of `α` that satisfies `cond` belongs to the range of `coe`. -/
  prf : ∀ x : α, cond x → ∃ y : β, coe y = x

instance : CanLift Int Nat (fun n : Nat ↦ n) (0 ≤ ·) :=
  ⟨fun n hn ↦ ⟨n.natAbs, Int.natAbs_of_nonneg hn⟩⟩

instance Pi.canLift (ι : Sort*) (α β : ι → Sort*) (coe : ∀ i, β i → α i) (P : ∀ i, α i → Prop)
    [∀ i, CanLift (α i) (β i) (coe i) (P i)] :
    CanLift (∀ i, α i) (∀ i, β i) (fun f i ↦ coe i (f i)) fun f ↦ ∀ i, P i (f i) where
  prf f hf := ⟨fun i => Classical.choose (CanLift.prf (f i) (hf i)),
    funext fun i => Classical.choose_spec (CanLift.prf (f i) (hf i))⟩

theorem Subtype.exists_pi_extension {ι : Sort*} {α : ι → Sort*} [ne : ∀ i, Nonempty (α i)]
    {p : ι → Prop} (f : ∀ i : Subtype p, α i) :
    ∃ g : ∀ i : ι, α i, (fun i : Subtype p => g i) = f := by
  haveI : DecidablePred p := fun i ↦ Classical.propDecidable (p i)
  exact ⟨fun i => if hi : p i then f ⟨i, hi⟩ else Classical.choice (ne i),
    funext fun i ↦ dif_pos i.2⟩

instance PiSubtype.canLift (ι : Sort*) (α : ι → Sort*) [∀ i, Nonempty (α i)] (p : ι → Prop) :
    CanLift (∀ i : Subtype p, α i) (∀ i, α i) (fun f i => f i) fun _ => True where
  prf f _ := Subtype.exists_pi_extension f

instance PiSubtype.canLift' (ι : Sort*) (α : Sort*) [Nonempty α] (p : ι → Prop) :
    CanLift (Subtype p → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι (fun _ => α) p

instance Subtype.canLift {α : Sort*} (p : α → Prop) :
    CanLift α { x // p x } Subtype.val p where prf a ha :=
  ⟨⟨a, ha⟩, rfl⟩

namespace Mathlib.Tactic

open Lean Parser Tactic Elab Tactic Meta

syntax (name := lift) "lift " term " to " term (" using " term)?

  (" with " ident (ppSpace colGt ident)? (ppSpace colGt ident)?)? : tactic

def Lift.getInst (old_tp new_tp : Expr) : MetaM (Expr × Expr × Expr) := do
  let coe ← mkFreshExprMVar (some <| .forallE `a new_tp old_tp .default)
  let p ← mkFreshExprMVar (some <| .forallE `a old_tp (.sort .zero) .default)
  let inst_type ← mkAppM ``CanLift #[old_tp, new_tp, coe, p]
  let inst ← synthInstance inst_type -- TODO: catch error
  return (← instantiateMVars p, ← instantiateMVars coe, ← instantiateMVars inst)

def Lift.main (e t : TSyntax `term) (hUsing : Option (TSyntax `term))
    (newVarName newEqName : Option (TSyntax `ident)) (keepUsing : Bool) : TacticM Unit :=
    withMainContext do
  -- Are we using a new variable for the lifted var?
  let isNewVar := !newVarName.isNone
  -- Name of the new hypothesis containing the equality of the lifted variable with the old one
  -- rfl if none is given
  let newEqName := (newEqName.map Syntax.getId).getD `rfl
  -- Was a new hypothesis given?
  let isNewEq := newEqName != `rfl
  let e ← elabTerm e none
  let goal ← getMainGoal
  if !(← inferType (← instantiateMVars (← goal.getType))).isProp then throwError
    "lift tactic failed. Tactic is only applicable when the target is a proposition."
  if newVarName == none ∧ !e.isFVar then throwError
    "lift tactic failed. When lifting an expression, a new variable name must be given"
  let (p, coe, inst) ← Lift.getInst (← inferType e) (← Term.elabType t)
  let prf ← match hUsing with
    | some h => elabTermEnsuringType h (p.betaRev #[e])
    | none => mkFreshExprMVar (some (p.betaRev #[e]))
  let newVarName ← match newVarName with
                 | some v => pure v.getId
                 | none   => e.fvarId!.getUserName
  let prfEx ← mkAppOptM ``CanLift.prf #[none, none, coe, p, inst, e, prf]
  let prfEx ← instantiateMVars prfEx
  let prfSyn ← prfEx.toSyntax
  -- if we have a new variable, but no hypothesis name was provided, we temporarily use a dummy
  -- hypothesis name
  let newEqName ← if isNewVar && !isNewEq then withMainContext <| getUnusedUserName `tmpVar
               else pure newEqName
  let newEqIdent := mkIdent newEqName
  -- Run rcases on the proof of the lift condition
  replaceMainGoal (← Lean.Elab.Tactic.RCases.rcases #[(none, prfSyn)]
    (.tuple Syntax.missing <| [newVarName, newEqName].map (.one Syntax.missing)) goal)
  -- if we use a new variable, then substitute it everywhere
  if isNewVar then
    for decl in ← getLCtx do
      if decl.userName != newEqName then
        let declIdent := mkIdent decl.userName
        -- The line below fails if $declIdent is there only once.
        evalTactic (← `(tactic| simp (config := {failIfUnchanged := false})
          only [← $newEqIdent] at $declIdent $declIdent))
    evalTactic (← `(tactic| simp (config := {failIfUnchanged := false}) only [← $newEqIdent]))
  -- Clear the temporary hypothesis used for the new variable name if applicable
  if isNewVar && !isNewEq then
    evalTactic (← `(tactic| clear $newEqIdent))
  -- Clear the "using" hypothesis if it's a variable in the context
  if prf.isFVar && !keepUsing then
    let some hUsingStx := hUsing | throwError "lift tactic failed: unreachable code was reached"
    evalTactic (← `(tactic| clear $hUsingStx))
    evalTactic (← `(tactic| try clear $hUsingStx))
  if hUsing.isNone then withMainContext <| setGoals (prf.mvarId! :: (← getGoals))

elab_rules : tactic

  | `(tactic| lift $e to $t $[using $h]?) => withMainContext <| Lift.main e t h none none false

elab_rules : tactic | `(tactic| lift $e to $t $[using $h]?

    with $newVarName) => withMainContext <| Lift.main e t h newVarName none false

elab_rules : tactic | `(tactic| lift $e to $t $[using $h]?

    with $newVarName $newEqName) => withMainContext <| Lift.main e t h newVarName newEqName false

elab_rules : tactic | `(tactic| lift $e to $t $[using $h]?

    with $newVarName $newEqName $newPrfName) => withMainContext do

  if h.isNone then Lift.main e t h newVarName newEqName false

  else

    let some h := h | unreachable!

    if h.raw == newPrfName then Lift.main e t h newVarName newEqName true

    else Lift.main e t h newVarName newEqName false

end Mathlib.Tactic
