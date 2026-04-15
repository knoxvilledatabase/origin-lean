/-
Extracted from Tactic/FunProp/Types.lean
Genuine: 18 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.FunProp.FunctionData
import Batteries.Data.RBMap.Basic

/-!
## `funProp`

this file defines environment extension for `funProp`
-/

namespace Mathlib

open Lean Meta

namespace Meta.FunProp

initialize registerTraceClass `Meta.Tactic.fun_prop

initialize registerTraceClass `Meta.Tactic.fun_prop.attr

initialize registerTraceClass `Debug.Meta.Tactic.fun_prop

inductive Origin where
  /-- It is a constant defined in the environment. -/
  | decl (name : Name)
  /-- It is a free variable in the local context. -/
  | fvar (fvarId : FVarId)
  deriving Inhabited, BEq

def Origin.name (origin : Origin) : Name :=
  match origin with
  | .decl name => name
  | .fvar id => id.name

def Origin.getValue (origin : Origin) : MetaM Expr := do
  match origin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => pure (.fvar id)

def ppOrigin {m} [Monad m] [MonadEnv m] [MonadError m] : Origin → m MessageData
  | .decl n => return m!"{← mkConstWithLevelParams n}"
  | .fvar n => return mkFVar n

def ppOrigin' (origin : Origin) : MetaM String := do
  match origin with
  | .fvar id => return s!"{← ppExpr (.fvar id)} : {← ppExpr (← inferType (.fvar id))}"
  | _ => pure (toString origin.name)

def FunctionData.getFnOrigin (fData : FunctionData) : Origin :=
  match fData.fn with
  | .fvar id => .fvar id
  | .const name _ => .decl name
  | _ => .decl Name.anonymous

def defaultNamesToUnfold : Array Name :=
  #[`id, `Function.comp, `Function.HasUncurry.uncurry, `Function.uncurry]

structure Config where
  /-- Maximum number of transitions between function properties. For example inferring continuity
  from differentiability and then differentiability from smoothness (`ContDiff ℝ ∞`) requires
  `maxTransitionDepth = 2`. The default value of one expects that transition theorems are
  transitively closed e.g. there is a transition theorem that infers continuity directly from
  smoothenss.

  Setting `maxTransitionDepth` to zero will disable all transition theorems. This can be very
  useful when `fun_prop` should fail quickly. For example when using `fun_prop` as discharger in
  `simp`.
  -/
  maxTransitionDepth := 1
  /-- Maximum number of steps `fun_prop` can take. -/
  maxSteps := 100000

deriving Inhabited, BEq

structure Context where
  /-- fun_prop config -/
  config : Config := {}
  /-- Name to unfold -/
  constToUnfold : Batteries.RBSet Name Name.quickCmp :=
    .ofArray defaultNamesToUnfold _
  /-- Custom discharger to satisfy theorem hypotheses. -/
  disch : Expr → MetaM (Option Expr) := fun _ => pure .none
  /-- current transition depth -/
  transitionDepth := 0

structure State where
  /-- Simp's cache is used as the `fun_prop` tactic is designed to be used inside of simp and
  utilize its cache. It holds successful goals. -/
  cache : Simp.Cache := {}
  /-- Cache storing failed goals such that they are not tried again. -/
  failureCache : ExprSet := {}
  /-- Count the number of steps and stop when maxSteps is reached. -/
  numSteps := 0
  /-- Log progress and failures messages that should be displayed to the user at the end. -/
  msgLog : List String := []

def Context.increaseTransitionDepth (ctx : Context) : Context :=
  {ctx with transitionDepth := ctx.transitionDepth + 1}

abbrev FunPropM := ReaderT FunProp.Context <| StateT FunProp.State MetaM

structure Result where
  /-- -/
  proof : Expr

def defaultUnfoldPred : Name → Bool :=
  defaultNamesToUnfold.contains

def unfoldNamePred : FunPropM (Name → Bool) := do
  let toUnfold := (← read).constToUnfold
  return fun n => toUnfold.contains n

def increaseSteps : FunPropM Unit := do
  let numSteps := (← get).numSteps
  let maxSteps := (← read).config.maxSteps
  if numSteps > maxSteps then
     throwError s!"fun_prop failed, maximum number({maxSteps}) of steps exceeded"
  modify (fun s => {s with numSteps := s.numSteps + 1})

def withIncreasedTransitionDepth {α} (go : FunPropM (Option α)) : FunPropM (Option α) := do
  let maxDepth := (← read).config.maxTransitionDepth
  let newDepth := (← read).transitionDepth + 1
  if newDepth > maxDepth then
    trace[Meta.Tactic.fun_prop]
   "maximum transition depth ({maxDepth}) reached
    if you want `fun_prop` to continue then increase the maximum depth with \
    `fun_prop (config := \{maxTransitionDepth := {newDepth}})`"
    return none
  else
    withReader (fun s => {s with transitionDepth := newDepth}) go

def logError (msg : String) : FunPropM Unit := do
  if (← read).transitionDepth = 0 then
    modify fun s =>
      {s with msgLog :=
        if s.msgLog.contains msg then
          s.msgLog
        else
          msg::s.msgLog}

end Meta.FunProp

end Mathlib
