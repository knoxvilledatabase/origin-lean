/-
Extracted from Tactic/Linter/FlexibleLinter.lean
Genuine: 16 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Lean.Elab.Command
import Mathlib.Init

noncomputable section

/-!
#  The "flexible" linter

The "flexible" linter makes sure that a "rigid" tactic (such as `rw`) does not act on the
output of a "flexible" tactic (such as `simp`).

For example, this ensures that, if you want to use `simp [...]` in the middle of a proof,
then you should replace `simp [...]` by one of
* a `suffices \"expr after simp\" by simpa` line;
* the output of `simp? [...]`, so that the final code contains `simp only [...]`;
* something else that does not involve `simp`!

Otherwise, the linter will complain.

Simplifying and appealing to a geometric intuition, you can imagine a (tactic) proof like a
directed graph, where
* each node is a local hypothesis or a goal in some metavariable and
* two hypotheses/goals are connected by an arrow if there is a tactic that modifies the source
  of the arrow into the target (this does not apply well to all tactics, but it does apply to
  a large number of them).
With this in mind, a tactic like `rw [lemma]` takes a *very specific* input and return a
*very predictable* output.
Such a tactic is "rigid". Any tactic is rigid, unless it is in `flexible` or `stoppers`.
Conversely, a tactic like `simp` acts on a wide variety of inputs and returns an output that
is possibly unpredictable: if later modifications adds a `simp`-lemma or some internals of
`simp` changes, the output of `simp` may change as well.
Such a tactic is `flexible`. Other examples are `split`, `abel`, `norm_cast`,...
Let's go back to the graph picture above.
* ✅️ [`rigid` --> `flexible`]
  A sequence `rw [lemma]; simp` is unlikely to break, since `rw [lemma]` produces the same output
  unless some *really major* change happens!
* ❌️ [`flexible` --> `rigid`]
  A sequence `simp; rw [lemma]` is instead more likely to break, since the goal after `simp` is
  subject to change by even a small, likely, modification of the `simp` set.
* ✅️ [`flexible` --> `flexible`]
  A sequence `simp; linarith` is also quite stable, since if `linarith` was able to close the
  goal with a "weaker" `simp`, it will likely still be able to close the goal with a `simp`
  that takes one further step.
* ✅️ [`flexible` --> `stopper`]
  Finally, a sequence `simp; ring_nf` is stable and, moreover, the output of `ring_nf` is a
  "normal form", which means that it is likely to produce an unchanged result, even if the initial
  input is different from the proof in its initial form.
  A stopper can be followed by a rigid tactic, "stopping" the spread of the flexible reach.

What the linter does is keeping track of nodes that are connected by `flexible` tactics and
makes sure that only `flexible` or `stoppers` follow them.
Such nodes are `Stained`.
Whenever it reaches a `stopper` edge, the target node is no longer `Stained` and it is
available again to `rigid` tactics.

Currently, the only tactics that "start" the bookkeeping are most forms of non-`only` `simp`s.
These are encoded by the `flexible?` predicate.
Future modifications of the linter may increase the scope of the `flexible?` predicate and
forbid a wider range of combinations.

## TODO
The example
```lean
example (h : 0 = 0) : True := by
  simp at h
  assumption
```
should trigger the linter, since `assumption` uses `h` that has been "stained" by `simp at h`.
However, `assumption` contains no syntax information for the location `h`, so the linter in its
current form does not catch this.

## Implementation notes

A large part of the code is devoted to tracking `FVar`s and `MVar`s between tactics.

For the `FVar`s, this follows the following heuristic:
* if the unique name of the `FVar` is preserved, then we use that;
* otherwise, if the `userName` of the `FVar` is preserved, then we use that;
* if neither is preserved, we drop the ball and stop tracking the `FVarId`.

For the `MVar`s, we use the information of `Lean.Elab.TacticInfo.goalsBefore` and
`Lean.Elab.TacticInfo.goalsAfter`.
By looking at the `mvar`s that are either only "before" or only "after", we focus on the
"active" goals.
We then propagate all the `FVarId`s that were present in the "before" goals to the "after" goals,
while leaving untouched the ones in the "inert" goals.
-/

open Lean Elab

namespace Mathlib.Linter

register_option linter.flexible : Bool := {

  defValue := false

  descr := "enable the flexible linter"

}

def flexible? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.simp #[_, _, _, only?, _, _] => only?[0].getAtomVal != "only"
  | .node _ ``Lean.Parser.Tactic.simpAll #[_, _, _, only?, _] => only?[0].getAtomVal != "only"
  | _ => false

end Mathlib.Linter

section goals_heuristic

namespace Lean.Elab.TacticInfo

/-!
###  Heuristics for determining goals goals that a tactic modifies what they become

The two definitions `goalsTargetedBy`, `goalsCreatedBy` extract a list of
`MVarId`s attempting to determine on which goals the tactic `t` is acting and what are the
resulting modified goals.
This is mostly based on the heuristic that the tactic will "change" an `MVarId`.
-/

def goalsTargetedBy (t : TacticInfo) : List MVarId :=
  t.goalsBefore.filter (·.name ∉ t.goalsAfter.map (·.name))

def goalsCreatedBy (t : TacticInfo) : List MVarId :=
  t.goalsAfter.filter (·.name ∉ t.goalsBefore.map (·.name))

end Lean.Elab.TacticInfo

end goals_heuristic

namespace Mathlib.Linter.Flexible

variable (take? : Syntax → Bool) in

partial

def extractCtxAndGoals : InfoTree →
    Array (Syntax × MetavarContext × MetavarContext × List MVarId × List MVarId)
  | .node k args =>
    let kargs := (args.map extractCtxAndGoals).foldl (· ++ ·) #[]
    if let .ofTacticInfo i := k then
      if take? i.stx && (i.stx.getRange? true).isSome then
        #[(i.stx, i.mctxBefore, i.mctxAfter, i.goalsTargetedBy, i.goalsCreatedBy)] ++ kargs
      else kargs
    else kargs
  | .context _ t => extractCtxAndGoals t
  | _ => default

inductive Stained
  | name     : Name → Stained
  | goal     : Stained
  | wildcard : Stained
  deriving Repr, Inhabited, DecidableEq, Hashable

instance : ToString Stained where
  toString | .name n => n.toString | .goal => "⊢" | .wildcard => "*"

partial

def toStained : Syntax → Std.HashSet Stained
  | .node _ _ arg => (arg.map toStained).foldl (.union) {}
  | .ident _ _ val _ => {.name val}
  | .atom _ val => match val with
                  | "*" => {.wildcard}
                  | "⊢" => {.goal}
                  | "|" => {.goal}
                  | _ => {}
  | _ => {}

partial

def getStained (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : Std.HashSet Stained :=
  match stx with
    | stx@(.node _ ``Lean.Parser.Tactic.location loc) =>
      if all? stx then {} else (loc.map toStained).foldl (·.union) {}
    | .node _ _ args => (args.map (getStained · all?)).foldl (·.union) {}
    | _ => default

def getStained! (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : Std.HashSet Stained :=
  let out := getStained stx all?
  if out.size == 0 then {.goal} else out

def Stained.toFMVarId (mv : MVarId) (lctx: LocalContext) : Stained → Array (FVarId × MVarId)
  | name n   => match lctx.findFromUserName? n with
                  | none => #[]
                  | some decl => #[(decl.fvarId, mv)]
  | goal     => #[(default, mv)]
  | wildcard => (lctx.getFVarIds.push default).map (·, mv)

def stoppers : Std.HashSet Name :=
  { -- "properly stopper tactics": the effect of these tactics is to return a normal form
    -- (or possibly be finishing tactics -- the ultimate normal form!
    -- finishing tactics could equally well be considered as `flexible`, but as there is
    -- no possibility of a follower anyway, it does not make a big difference.)
    ``Lean.Parser.Tactic.tacticSorry,
    ``Lean.Parser.Tactic.tacticRepeat_,
    ``Lean.Parser.Tactic.tacticStop_,
    `Mathlib.Tactic.Abel.abelNF,
    `Mathlib.Tactic.RingNF.ringNF,
    -- "continuators": the *effect* of these tactics is similar the "properly stoppers" above,
    -- though they typically wrap other tactics inside them.
    -- The linter ignores the wrapper, but does recurse into the enclosed tactics
    ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeq,
    ``Lean.Parser.Term.byTactic,
    `by,
    ``Lean.Parser.Tactic.tacticTry_,
    `choice,  -- involved in `first`
    ``Lean.Parser.Tactic.allGoals,
    `Std.Tactic.«tacticOn_goal-_=>_»,
    ``Lean.Parser.Tactic.«tactic_<;>_»,
    ``cdotTk,
    ``cdot }

def flexible : Std.HashSet Name :=
  { ``Lean.Parser.Tactic.simp,
    ``Lean.Parser.Tactic.simpAll,
    ``Lean.Parser.Tactic.simpa,
    ``Lean.Parser.Tactic.dsimp,
    ``Lean.Parser.Tactic.constructor,
    ``Lean.Parser.Tactic.congr,
    ``Lean.Parser.Tactic.done,
    ``Lean.Parser.Tactic.tacticRfl,
    ``Lean.Parser.Tactic.omega,
    `Mathlib.Tactic.Abel.abel,
    `Mathlib.Tactic.RingNF.ring,
    `Mathlib.Tactic.normNum,
    `linarith,
    `nlinarith,
    ``Lean.Parser.Tactic.tacticNorm_cast_,
    `Aesop.Frontend.Parser.aesopTactic,
    `Mathlib.Tactic.Tauto.tauto,
    `Mathlib.Meta.FunProp.funPropTacStx,
    `Lean.Parser.Tactic.split,
    `Mathlib.Tactic.splitIfs }

def usesGoal? : SyntaxNodeKind → Bool
  | ``Lean.Parser.Tactic.cases => false
  | `Mathlib.Tactic.cases' => false
  | ``Lean.Parser.Tactic.obtain => false
  | ``Lean.Parser.Tactic.tacticHave_ => false
  | ``Lean.Parser.Tactic.rcases => false
  | ``Lean.Parser.Tactic.specialize => false
  | ``Lean.Parser.Tactic.subst => false
  | ``«tacticBy_cases_:_» => false
  | ``Lean.Parser.Tactic.induction => false
  | _ => true

def getFVarIdCandidates (fv : FVarId) (name : Name) (lctx : LocalContext) : Array FVarId :=
  #[lctx.find? fv, lctx.findFromUserName? name].reduceOption.map (·.fvarId)

/-!
Tactics often change the name of the current `MVarId`, as well as the names of the `FVarId`s
appearing in their local contexts.
The function `reallyPersist` makes an attempt at "tracking" pairs `(fvar, mvar)` across a
simultaneous change represented by an "old" list of `MVarId`s and the corresponding
`MetavarContext` and a new one.

This arises in the context of the information encoded in the `InfoTree`s when processing a
tactic proof.
-/

def persistFVars (fv : FVarId) (before after : LocalContext) : FVarId :=
  let ldecl := (before.find? fv).getD default
  let name := ldecl.userName
  (getFVarIdCandidates fv name after).getD 0 default

def reallyPersist
    (fmvars : Array (FVarId × MVarId)) (mvs0 mvs1 : List MVarId) (ctx0 ctx1 : MetavarContext) :
    Array (FVarId × MVarId) := Id.run do
  -- split the input `fmvars` into
  -- * the `active` ones, whose `mvar` appears in `mvs0` and
  -- * the `inert` ones, the rest.
  -- `inert` gets copied unchanged, while we transform `active`
  let (active, inert) := fmvars.partition fun (_, mv) => mvs0.contains mv
  let mut new := #[]
  for (fvar, mvar) in active do       -- for each `active` pair `(fvar, mvar)`
    match ctx0.decls.find? mvar with  -- check if `mvar` is managed by `ctx0` (it should be)
      | none => -- the `mvar` is not managed by `ctx0`: no change
        new := new.push (fvar, mvar)
      | some mvDecl0 => -- the `mvar` *is* managed by `ctx0`: push the pair `(fvar, mvar)` through
        for mv1 in mvs1 do  -- for each new `MVarId` in `mvs1`
          match ctx1.decls.find? mv1 with  -- check if `mv1` is managed by `ctx1` (it should be)
            | none => dbg_trace "'really_persist' could this happen?" default -- ??? maybe `.push`?
            | some mvDecl1 =>  -- we found a "new" declaration
              let persisted_fv := persistFVars fvar mvDecl0.lctx mvDecl1.lctx  -- persist `fv`
              new := new.push (persisted_fv, mv1)
  return inert ++ new

def flexibleLinter : Linter where run := withSetOptionIn fun _stx => do
  unless Linter.getLinterValue linter.flexible (← getOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let x := trees.toList.map (extractCtxAndGoals (fun _ => true))
  -- `stains` records pairs `(location, mvar)`, where
  -- * `location` is either a hypothesis or the main goal modified by a flexible tactic and
  -- * `mvar` is the metavariable containing the modified location
  let mut stains : Array ((FVarId × MVarId) × (Stained × Syntax)) := .empty
  let mut msgs : Array (Syntax × Syntax × Stained) := #[]
  for d in x do for (s, ctx0, ctx1, mvs0, mvs1) in d do
    let skind := s.getKind
    if stoppers.contains skind then continue
    let shouldStain? := flexible? s && mvs1.length == mvs0.length
    for d in getStained! s do
      if shouldStain? then
        for currMVar1 in mvs1 do
          let lctx1 := ((ctx1.decls.find? currMVar1).getD default).lctx
          let locsAfter := d.toFMVarId currMVar1 lctx1

          for l in locsAfter do
            stains := stains.push (l, (d, s))

      else
        let stained_in_syntax := if usesGoal? skind then (toStained s).insert d else toStained s
        if !flexible.contains skind then
          for currMv0 in mvs0 do
            let lctx0 := ((ctx0.decls.find? currMv0).getD default).lctx
            let mut foundFvs : Std.HashSet (FVarId × MVarId):= {}
            for st in stained_in_syntax do
              for d in st.toFMVarId currMv0 lctx0 do
                if !foundFvs.contains d then foundFvs := foundFvs.insert d
            for l in foundFvs do
              if let some (_stdLoc, (st, kind)) := stains.find? (Prod.fst · == l) then
                msgs := msgs.push (s, kind, st)

      -- tactics often change the name of the current `MVarId`, so we migrate the `FvarId`s
      -- in the "old" `mvars` to the "same" `FVarId` in the "new" `mvars`
      let mut new : Array ((FVarId × MVarId) × (Stained × Syntax)) := .empty
      for (fv, (stLoc, kd)) in stains do
        let psisted := reallyPersist #[fv] mvs0 mvs1 ctx0 ctx1
        if psisted == #[] && mvs1 != [] then
          new := new.push (fv, (stLoc, kd))
          dbg_trace "lost {((fv.1.name, fv.2.name), stLoc, kd)}"
        for p in psisted do new := new.push (p, (stLoc, kd))
      stains := new

  for (s, stainStx, d) in msgs do
    Linter.logLint linter.flexible stainStx m!"'{stainStx}' is a flexible tactic modifying '{d}'…"
    logInfoAt s m!"… and '{s}' uses '{d}'!"

initialize addLinter flexibleLinter

end Mathlib.Linter.Flexible
