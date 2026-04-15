/-
Extracted from Tactic/WLOG.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.Core
import Lean.Meta.Tactic.Cases

/-!

# Without loss of generality tactic

The tactic `wlog h : P` will add an assumption `h : P` to the main goal,
and add a new goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).

The new goal will be placed at the top of the goal stack.

-/

namespace Mathlib.Tactic

open Lean Meta Elab Term Tactic MetavarContext.MkBinding

structure WLOGResult where
  /-- The `reductionGoal` requires showing that the case `h : ¬ P` can be reduced to the case where
  `P` holds. It has two additional assumptions in its context:

  * `h : ¬ P`: the assumption that `P` does not hold
  * `H`: the statement that in the original context `P` suffices to prove the goal.
  -/
  reductionGoal    : MVarId
  /-- The pair `(HFVarId, negHypFVarId)` of `FVarIds` for `reductionGoal`:

  * `HFVarId`: `H`, the statement that in the original context `P` suffices to prove the goal.
  * `negHypFVarId`: `h : ¬ P`, the assumption that `P` does not hold
  -/
  reductionFVarIds : FVarId × FVarId
  /-- The original goal with the additional assumption `h : P`. -/
  hypothesisGoal   : MVarId
  /-- The `FVarId` of the hypothesis `h` in `hypothesisGoal` -/
  hypothesisFVarId : FVarId
  /-- The array of `FVarId`s that was reverted to produce the reduction hypothesis `H` in
  `reductionGoal`, which are still present in the context of `reductionGoal` (but not necessarily
  `hypothesisGoal`). -/
  revertedFVarIds  : Array FVarId

open private withFreshCache mkAuxMVarType from Lean.MetavarContext in

def _root_.Lean.MVarId.wlog (goal : MVarId) (h : Option Name) (P : Expr)
    (xs : Option (TSyntaxArray `ident) := none) (H : Option Name := none) :
    TacticM WLOGResult := goal.withContext do
  goal.checkNotAssigned `wlog
  let H := H.getD `this
  let inaccessible := h.isNone
  let h := h.getD `h
  /- Compute the type for H and keep track of the FVarId's reverted in doing so. (Do not modify the
  tactic state.) -/
  let HSuffix := Expr.forallE h P (← goal.getType) .default
  let fvars ← getFVarIdsAt goal xs
  let fvars := fvars.map Expr.fvar
  let lctx := (← goal.getDecl).lctx
  let (revertedFVars, HType) ← liftMkBindingM fun ctx => (do
    let f ← collectForwardDeps lctx fvars
    let revertedFVars := filterOutImplementationDetails lctx (f.map Expr.fvarId!)
    let HType ← withFreshCache do mkAuxMVarType lctx (revertedFVars.map Expr.fvar) .natural HSuffix
    return (revertedFVars, HType))
      { preserveOrder := false, mainModule := ctx.mainModule }
  /- Set up the goal which will suppose `h`; this begins as a goal with type H (hence HExpr), and h
  is obtained through `introNP` -/
  let HExpr ← mkFreshExprSyntheticOpaqueMVar HType
  let hGoal := HExpr.mvarId!
  /- Begin the "reduction goal" which will contain hypotheses `H` and `¬h`. For now, it only
  contains `H`. Keep track of that hypothesis' FVarId. -/
  let (HFVarId, reductionGoal) ←
    goal.assertHypotheses #[{ userName := H, type := HType, value := HExpr }]
  let HFVarId := HFVarId[0]!
  /- Clear the reverted fvars from the branch that will contain `h` as a hypothesis. -/
  let hGoal ← hGoal.tryClearMany revertedFVars
  /- Introduce all of the reverted fvars to the context in order to restore the original target as
  well as finally introduce the hypothesis `h`. -/
  let (_, hGoal) ← hGoal.introNP revertedFVars.size
  -- keep track of the hypothesis' FVarId
  let (hFVar, hGoal) ← if inaccessible then hGoal.intro1 else hGoal.intro1P
  /- Split the reduction goal by cases on `h`. Keep the one with `¬h` as the reduction goal,
  and prove the easy goal by applying `H` to all its premises, which are fvars in the context. -/
  let (⟨easyGoal, hyp⟩, ⟨reductionGoal, negHyp⟩) ←
    reductionGoal.byCases P <| if inaccessible then `_ else h
  easyGoal.withContext do
    -- Exclude ldecls from the `mkAppN` arguments
    let HArgFVarIds ← revertedFVars.filterM (notM ·.isLetVar)
    let HApp ← instantiateMVars <|
      mkAppN (.fvar HFVarId) (HArgFVarIds.map .fvar) |>.app (.fvar hyp)
    ensureHasNoMVars HApp
    easyGoal.assign HApp
  return ⟨reductionGoal, (HFVarId, negHyp), hGoal, hFVar, revertedFVars⟩

syntax (name := wlog) "wlog " binderIdent " : " term

  (" generalizing" (ppSpace colGt ident)*)? (" with " binderIdent)? : tactic

elab_rules : tactic

| `(tactic| wlog $h:binderIdent : $P:term $[ generalizing $xs*]? $[ with $H:ident]?) =>

  withMainContext do

  let H := H.map (·.getId)

  let h := match h with

  | `(binderIdent|$h:ident) => some h.getId

  | _ => none

  let P ← elabType P

  let goal ← getMainGoal

  let { reductionGoal, hypothesisGoal .. } ← goal.wlog h P xs H

  replaceMainGoal [reductionGoal, hypothesisGoal]

end Mathlib.Tactic
