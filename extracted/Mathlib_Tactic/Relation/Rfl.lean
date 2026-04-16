/-
Extracted from Tactic/Relation/Rfl.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Meta.Tactic.Rfl

noncomputable section

/-!
# `Lean.MVarId.liftReflToEq`

Convert a goal of the form `x ~ y` into the form `x = y`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute `[refl]`.
If this can't be done, returns the original `MVarId`.
-/

namespace Mathlib.Tactic

open Lean Meta Elab Tactic Rfl

def rflTac : TacticM Unit :=
  withMainContext do liftMetaFinishingTactic (·.applyRfl)

def _root_.Lean.Expr.relSidesIfRefl? (e : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  if let some (_, lhs, rhs) := e.eq? then
    return (``Eq, lhs, rhs)
  if let some (lhs, rhs) := e.iff? then
    return (``Iff, lhs, rhs)
  if let some (_, lhs, _, rhs) := e.heq? then
    return (``HEq, lhs, rhs)
  if let .app (.app rel lhs) rhs := e then
    unless (← (reflExt.getState (← getEnv)).getMatch rel reflExt.config).isEmpty do
      match rel.getAppFn.constName? with
      | some n => return some (n, lhs, rhs)
      | none => return none
  return none

end Mathlib.Tactic
