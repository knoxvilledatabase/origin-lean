/-
Extracted from Tactic/Recover.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init

/-!
# The `recover` tactic modifier

This defines the `recover` tactic modifier, which can be used to debug cases where goals
are not closed correctly. `recover tacs` for a tactic (or tactic sequence) `tacs`
applies the tactics and then adds goals
that are not closed, starting from the original goal.
-/

namespace Mathlib.Tactic

open Lean (HashSet)

open Lean Meta Elab Tactic

partial def getUnassignedGoalMVarDependencies (mvarId : MVarId) :
    MetaM (Std.HashSet MVarId) :=
  return (← go mvarId |>.run {}).snd
  where
    /-- auxiliary function for `getUnassignedGoalMVarDependencies` -/
    addMVars (e : Expr) : StateRefT (Std.HashSet MVarId) MetaM Unit := do
      let mvars ← getMVars e
      let mut s ← get
      set ({} : Std.HashSet MVarId) -- Ensure that `s` is not shared.
      for mvarId in mvars do
        unless ← mvarId.isDelayedAssigned do
          s := s.insert mvarId
      set s
      mvars.forM go
    /-- auxiliary function for `getUnassignedGoalMVarDependencies` -/
    go (mvarId : MVarId) : StateRefT (Std.HashSet MVarId) MetaM Unit :=
      withIncRecDepth do
        let mdecl ← mvarId.getDecl
        addMVars mdecl.type
        for ldecl in mdecl.lctx do
          addMVars ldecl.type
          if let (some val) := ldecl.value? then
            addMVars val
        if let (some ass) ← getDelayedMVarAssignment? mvarId then
          let pendingMVarId := ass.mvarIdPending
          unless ← pendingMVarId.isAssigned <||> pendingMVarId.isDelayedAssigned do
            modify (·.insert pendingMVarId)
          go pendingMVarId

elab "recover " tacs:tacticSeq : tactic => do

  let originalGoals ← getGoals

  evalTactic tacs

  let mut unassigned : Std.HashSet MVarId := {}

  for mvarId in originalGoals do

    unless ← mvarId.isAssigned <||> mvarId.isDelayedAssigned do

      unassigned := unassigned.insert mvarId

    let unassignedMVarDependencies ← getUnassignedGoalMVarDependencies mvarId

    unassigned := unassigned.insertMany unassignedMVarDependencies.toList

  setGoals <| ((← getGoals) ++ unassigned.toList).eraseDups

end Mathlib.Tactic
