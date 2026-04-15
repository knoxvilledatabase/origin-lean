/-
Extracted from Lean/GoalsLocation.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Meta.Tactic.Util
import Lean.SubExpr

/-! This file defines some functions for dealing with `SubExpr.GoalsLocation`. -/

namespace Lean.SubExpr.GoalsLocation

def rootExpr : GoalsLocation → MetaM Expr
  | ⟨_, .hyp fvarId⟩        => fvarId.getType
  | ⟨_, .hypType fvarId _⟩  => fvarId.getType
  | ⟨_, .hypValue fvarId _⟩ => do return (← fvarId.getDecl).value
  | ⟨mvarId, .target _⟩     => mvarId.getType

def pos : GoalsLocation → Pos
  | ⟨_, .hyp _⟩          => .root
  | ⟨_, .hypType _ pos⟩  => pos
  | ⟨_, .hypValue _ pos⟩ => pos
  | ⟨_, .target pos⟩     => pos

def location : GoalsLocation → MetaM (Option Name)
  | ⟨_, .hyp fvarId⟩        => some <$> fvarId.getUserName
  | ⟨_, .hypType fvarId _⟩  => some <$> fvarId.getUserName
  | ⟨_, .hypValue fvarId _⟩ => some <$> fvarId.getUserName
  | ⟨_, .target _⟩          => return none

end Lean.SubExpr.GoalsLocation
