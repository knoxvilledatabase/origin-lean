/-
Extracted from Util/Tactic.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.MetavarContext

noncomputable section

/-!
# Miscellaneous helper functions for tactics.

[TODO] Ideally we would find good homes for everything in this file, eventually removing it.
-/

namespace Mathlib.Tactic

open Lean Meta Tactic

variable {m : Type → Type}

def modifyMetavarDecl [MonadMCtx m] (mvarId : MVarId)
    (f : MetavarDecl → MetavarDecl) : m Unit :=
  modifyMCtx fun mctx ↦
    match mctx.decls.find? mvarId with
    | none => mctx
    | some mdecl => { mctx with decls := mctx.decls.insert mvarId (f mdecl) }

def modifyTarget [MonadMCtx m] (mvarId : MVarId) (f : Expr → Expr) : m Unit :=
  modifyMetavarDecl mvarId fun mdecl ↦
    { mdecl with type := f mdecl.type }

def modifyLocalContext [MonadMCtx m] (mvarId : MVarId)
    (f : LocalContext → LocalContext) : m Unit :=
  modifyMetavarDecl mvarId fun mdecl ↦
    { mdecl with lctx := f mdecl.lctx }

def modifyLocalDecl [MonadMCtx m] (mvarId : MVarId) (fvarId : FVarId)
    (f : LocalDecl → LocalDecl) : m Unit :=
  modifyLocalContext mvarId fun lctx ↦ lctx.modifyLocalDecl fvarId f

end Mathlib.Tactic
