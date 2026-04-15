/-
Extracted from Tactic/ApplyFun.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Lean.Expr.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Hom.Basic

/-!
# The `apply_fun` tactic.

Apply a function to an equality or inequality in either a local hypothesis or the goal.

## Porting notes
When the `mono` tactic has been ported we can attempt to automatically discharge `Monotone f` goals.
-/

namespace Mathlib.Tactic

open Lean Parser Tactic Elab Tactic Meta

initialize registerTraceClass `apply_fun

def applyFunHyp (f : Term) (using? : Option Term) (h : FVarId) (g : MVarId) :
    TacticM (List MVarId) := do
  let using? ← using?.mapM (elabTerm · none)
  let d ← h.getDecl
  let (prf, newGoals) ← match (← whnfR (← instantiateMVars d.type)).getAppFnArgs with
    | (``Eq, #[_, lhs, rhs]) => do
      let (eq', gs) ←
        withCollectingNewGoalsFrom (parentTag := ← g.getTag) (tagSuffix := `apply_fun) <|
        withoutRecover <| runTermElab <| do
          let f ← Term.elabTerm f none
          let lhs' ← Term.elabAppArgs f #[] #[.expr lhs] none false false
          let rhs' ← Term.elabAppArgs f #[] #[.expr rhs] none false false
          unless ← isDefEq (← inferType lhs') (← inferType rhs') do
            let msg ← mkHasTypeButIsExpectedMsg (← inferType rhs') (← inferType lhs')
            throwError "In generated equality, right-hand side {msg}"
          let eq ← mkEq lhs'.headBeta rhs'.headBeta
          Term.synthesizeSyntheticMVarsUsingDefault
          instantiateMVars eq
      let mvar ← mkFreshExprMVar eq'
      let [] ← mvar.mvarId!.congrN! | throwError "`apply_fun` could not construct congruence"
      pure (mvar, gs)
    | (``Not, #[P]) =>
      match (← whnfR P).getAppFnArgs with
      | (``Eq, _) =>
        let (injective_f, newGoals) ← match using? with
          -- Use the expression passed with `using`
          | some r => pure (r, [])
          -- Create a new `Injective f` goal
          | none => do
            let f ← elabTermForApply f
            let ng ← mkFreshExprMVar (← mkAppM ``Function.Injective #[f])
            -- TODO attempt to solve this goal using `mono` when it has been ported,
            -- via `synthesizeUsing`.
            pure (ng, [ng.mvarId!])
        pure (← mkAppM' (← mkAppM ``Function.Injective.ne #[injective_f]) #[d.toExpr], newGoals)
      | _ => throwError
        "apply_fun can only handle negations of equality."
    | (``LT.lt, _) =>
      let (strict_monotone_f, newGoals) ← match using? with
        -- Use the expression passed with `using`
        | some r => pure (r, [])
        -- Create a new `StrictMono f` goal
        | none => do
          let f ← elabTermForApply f
          let ng ← mkFreshExprMVar (← mkAppM ``StrictMono #[f])
          -- TODO attempt to solve this goal using `mono` when it has been ported,
          -- via `synthesizeUsing`.
          pure (ng, [ng.mvarId!])
      pure (← mkAppM' strict_monotone_f #[d.toExpr], newGoals)
    | (``LE.le, _) =>
      let (monotone_f, newGoals) ← match using? with
        -- Use the expression passed with `using`
        | some r => pure (r, [])
        -- Create a new `Monotone f` goal
        | none => do
          let f ← elabTermForApply f
          let ng ← mkFreshExprMVar (← mkAppM ``Monotone #[f])
          -- TODO attempt to solve this goal using `mono` when it has been ported,
          -- via `synthesizeUsing`.
          pure (ng, [ng.mvarId!])
      pure (← mkAppM' monotone_f #[d.toExpr], newGoals)
    | _ => throwError
      "apply_fun can only handle hypotheses of the form `a = b`, `a ≠ b`, `a ≤ b`, `a < b`."

  let g ← g.clear h
  let (_, g) ← g.note d.userName prf
  return g :: newGoals

def applyFunTargetFailure (f : Term) : MetaM (List MVarId) := do
  throwError "`apply_fun` could not apply `{f}` to the main goal."

def maybeProveInjective (ginj : Expr) (using? : Option Expr) : MetaM Bool := do
  -- Try the `using` clause
  if let some u := using? then
    if ← isDefEq ginj u then
      ginj.mvarId!.assign u
      return true
    else
      let err ← mkHasTypeButIsExpectedMsg (← inferType u) (← inferType ginj)
      throwError "Using clause {err}"
  -- Try an assumption
  if ← ginj.mvarId!.assumptionCore then
    return true
  -- Try using that this is an equivalence
  -- Note: if `f` is itself a metavariable, this can cause it to become an equivalence;
  -- perhaps making sure `f` is an equivalence would be correct, but maybe users
  -- shouldn't do `apply_fun _`.
  let ok ← observing? do
    let [] ← ginj.mvarId!.apply (← mkConstWithFreshMVarLevels ``Equiv.injective) | failure
  if ok.isSome then return true
  return false

alias ⟨ApplyFun.le_of_le, _⟩ := OrderIso.le_iff_le

alias ⟨ApplyFun.lt_of_lt, _⟩ := OrderIso.lt_iff_lt

def applyFunTarget (f : Term) (using? : Option Term) (g : MVarId) : TacticM (List MVarId) := do
  -- handle applying a two-argument theorem whose first argument is f
  let handle (thm : Name) : TacticM (List MVarId) := do
    let ng ← mkFreshExprMVar none
    let (pf, gs) ←
      withCollectingNewGoalsFrom (parentTag := ← g.getTag) (tagSuffix := `apply_fun) <|
      withoutRecover <| runTermElab do
        -- This coerces `f` to be a function as necessary:
        let pf ← Term.elabTermEnsuringType (← `($(mkIdent thm) $f $(← Term.exprToSyntax ng)))
                    (← g.getType)
        Term.synthesizeSyntheticMVarsUsingDefault
        return pf
    g.assign pf
    return ng.mvarId! :: gs
  let gty ← whnfR (← instantiateMVars (← g.getType))
  match gty.getAppFnArgs with
  | (``Not, #[p]) => match p.getAppFnArgs with
    | (``Eq, #[_, _, _]) => handle ``ne_of_apply_ne
    | _ => applyFunTargetFailure f
  | (``LE.le, _)
  | (``GE.ge, _) => handle ``ApplyFun.le_of_le
  | (``LT.lt, _)
  | (``GT.gt, _) => handle ``ApplyFun.lt_of_lt
  | (``Eq, #[_, _, _]) => do
    -- g' is for the `f lhs = f rhs` goal
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkFreshTypeMVar) (← g.getTag)
    -- ginj is for the `Injective f` goal
    let ginj ← mkFreshExprSyntheticOpaqueMVar (← mkFreshTypeMVar) (appendTag (← g.getTag) `inj)
    -- `withCollectingNewGoalsFrom` does not expect the goal to be closed, so here is "the goal"
    let gDefer ← mkFreshExprMVar (← g.getType)
    let (_, gs) ←
      withCollectingNewGoalsFrom (parentTag := ← g.getTag) (tagSuffix := `apply_fun) <|
      withoutRecover <| runTermElab do
        let inj ← Term.elabTerm (← ``(Function.Injective $f)) none
        _ ← isDefEq (← inferType ginj) inj
        let pf ← Term.elabAppArgs ginj #[] #[.expr g'] (← g.getType) false false
        let pf ← Term.ensureHasType (← g.getType) pf
        -- In the current context, let's try proving injectivity since it might fill in some holes
        let using? ← using?.mapM (Term.elabTerm · (some inj))
        _ ← withAssignableSyntheticOpaque <| maybeProveInjective ginj using?
        Term.synthesizeSyntheticMVarsUsingDefault
        gDefer.mvarId!.assign pf
        -- Return `inj` so that `withCollectingNewGoalsFrom` detects holes in `f`.
        return inj
    g.assign gDefer
    -- Perhaps ginj was assigned by `proveInjective`, but it's OK putting `ginj` in the list.
    return [g'.mvarId!, ginj.mvarId!] ++ gs
  | _ => applyFunTargetFailure f

syntax (name := applyFun) "apply_fun " term (location)? (" using " term)? : tactic

elab_rules : tactic | `(tactic| apply_fun $f $[$loc]? $[using $P]?) => do

  withLocation (expandOptLocation (Lean.mkOptionalNode loc))

    (atLocal := fun h ↦ do replaceMainGoal <| ← applyFunHyp f P h (← getMainGoal))

    (atTarget := withMainContext do

      replaceMainGoal <| ← applyFunTarget f P (← getMainGoal))

    (failed := fun _ ↦ throwError "apply_fun failed")

end Mathlib.Tactic
