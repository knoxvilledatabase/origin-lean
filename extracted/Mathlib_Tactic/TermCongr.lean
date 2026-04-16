/-
Extracted from Tactic/TermCongr.lean
Genuine: 31 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Meta.CongrTheorems
import Mathlib.Logic.Basic
import Mathlib.Tactic.CongrExclamation

noncomputable section

/-! # `congr(...)` congruence quotations

This module defines a term elaborator for generating congruence lemmas
from patterns written using quotation syntax.
One can write `congr($hf $hx)` with `hf : f = f'` and `hx : x = x'` to get `f x = f' x'`.
While in simple cases it might be possible to use `congr_arg` or `congr_fun`,
congruence quotations are more general,
since for example `f` could have implicit arguments, complicated dependent types,
and subsingleton instance arguments such as `Decidable` or `Fintype`.

The implementation strategy is the following:

1. The pattern is elaborated twice, once with each hole replaced by the LHS
   and again with each hole replaced by the RHS. We do not force the hole to
   have any particular type while elaborating, but if the hole has a type
   with an obvious LHS or RHS, then we propagate this information outward.
   We use `Mathlib.Tactic.TermCongr.cHole` with metadata for these replacements
   to hold onto the hole itself.
2. Once the pattern has been elaborated twice,
   we unify them against the respective LHS and RHS of the target type
   if the target has a type with an obvious LHS and RHS.
   This can fill in some metavariables and help typeclass inference make progress.
3. Then we simultaneously walk along the elaborated LHS and RHS expressions
   to generate a congruence.
   When we reach `cHole`s, we make sure they elaborated in a compatible way.
   Each `Expr` type has some logic to come up with a suitable congruence.
   For applications we use a version of `Lean.Meta.mkHCongrWithArity` that tries
   to fill in some of the equality proofs using subsingleton lemmas.

The point of elaborating the expression twice is that we let the elaborator handle
activities like synthesizing instances, etc., specialized to LHS or RHS, without trying
to derive one side from the other.

During development there was a version using `simp` transformations, but there was
no way to inform `simp` about the expected RHS, which could cause `simp` to fail because
it eagerly wants to solve for instance arguments. The current version is able to use the
expected LHS and RHS to fill in arguments before solving for instance arguments.
-/

universe u

namespace Mathlib.Tactic.TermCongr

open Lean Elab Meta

initialize registerTraceClass `Elab.congr

syntax (name := termCongr) "congr(" withoutForbidden(ppDedentIfGrouped(term)) ")" : term

/-! ### Congruence holes

This section sets up the way congruence holes are elaborated for `congr(...)` quotations.
The basic problem is that if we have `$h` with `h : x = y`, we need to elaborate it once
as `x` and once as `y`, and in both cases the term needs to remember that it's associated
to `h`.
-/

private def congrHoleForLhsKey : Name := decl_name%

private def congrHoleIndex : Name := decl_name%

@[reducible, nolint unusedArguments]
def cHole {α : Sort u} (val : α) {p : Prop} (_pf : p) : α := val

@[app_unexpander cHole] def unexpandCHole : Lean.PrettyPrinter.Unexpander
  | `($_ $val $_) => pure val
  | _ => throw ()

def mkCHole (forLhs : Bool) (val pf : Expr) : MetaM Expr := do
  -- Create a metavariable to bump the mvarCounter.
  discard <| mkFreshTypeMVar
  let d : MData := KVMap.empty
    |>.insert congrHoleForLhsKey forLhs
    |>.insert congrHoleIndex (← getMCtx).mvarCounter
  return Expr.mdata d <| ← mkAppM ``cHole #[val, pf]

def cHole? (e : Expr) (mvarCounterSaved? : Option Nat := none) : Option (Bool × Expr × Expr) := do
  match e with
  | .mdata d e' =>
    let forLhs : Bool ← d.get? congrHoleForLhsKey
    let mvarCounter : Nat ← d.get? congrHoleIndex
    if let some mvarCounterSaved := mvarCounterSaved? then
      guard <| mvarCounterSaved ≤ mvarCounter
    let #[_, val, _, pf] := e'.getAppArgs | failure
    return (forLhs, val, pf)
  | _ => none

def hasCHole (mvarCounterSaved : Nat) (e : Expr) : Option Expr :=
  e.find? fun e' => (cHole? e' mvarCounterSaved).isSome

def removeCHoles (e : Expr) : Expr :=
  e.replace fun e' => if let some (_, val, _) := cHole? e' then val else none

def elabCHole (h : Syntax) (forLhs : Bool) (expectedType? : Option Expr) : Term.TermElabM Expr := do
  let pf ← Term.elabTerm h none
  let pfTy ← inferType pf
  -- Ensure that `pfTy` is a proposition
  unless ← isDefEq (← inferType pfTy) (.sort .zero) do
    throwError "Hole has type{indentD pfTy}\nbut is expected to be a Prop"
  if let some (_, lhs, _, rhs) := (← whnf pfTy).sides? then
    let val := if forLhs then lhs else rhs
    if let some expectedType := expectedType? then
      -- Propagate type hint:
      discard <| isDefEq expectedType (← inferType val)
    mkCHole forLhs val pf
  else
    -- Since `pf` doesn't yet have sides, we resort to the value and the proof being decoupled.
    -- These will be unified during congruence generation.
    mkCHole forLhs (← mkFreshExprMVar expectedType?) pf

syntax (name := cHoleExpand) "cHole% " (&"lhs" <|> &"rhs") term : term

@[term_elab cHoleExpand, inherit_doc cHoleExpand]
def elabCHoleExpand : Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(cHole% lhs $h) => elabCHole h true expectedType?
  | `(cHole% rhs $h) => elabCHole h false expectedType?
  | _ => throwUnsupportedSyntax

def processAntiquot (t : Term) (expand : Term → Term.TermElabM Term) : Term.TermElabM Term := do
  let t' ← t.raw.replaceM fun s => do
    if s.isAntiquots then
      let ks := s.antiquotKinds
      unless ks.any (fun (k, _) => k == `term) do
        throwErrorAt s "Expecting term"
      let h : Term := ⟨s.getCanonicalAntiquot.getAntiquotTerm⟩
      expand h
    else
      pure none
  return ⟨t'⟩

def elaboratePattern (t : Term) (expectedType? : Option Expr) (forLhs : Bool) :
    Term.TermElabM Expr :=
  Term.withoutErrToSorry do
    let t' ← processAntiquot t (fun h => if forLhs then `(cHole% lhs $h) else `(cHole% rhs $h))
    Term.elabTermEnsuringType t' expectedType?

/-! ### Congruence generation -/

def mkEqForExpectedType (expectedType? : Option Expr) : MetaM Expr := do
  let u ← mkFreshLevelMVar
  let ty ← mkFreshExprMVar (mkSort u)
  let eq := mkApp3 (mkConst ``Eq [u]) ty (← mkFreshExprMVar ty) (← mkFreshExprMVar ty)
  if let some expectedType := expectedType? then
    unless ← isDefEq expectedType eq do
      throwError m!"Type{indentD expectedType}\nis expected to be an equality."
  return eq

def mkHEqForExpectedType (expectedType? : Option Expr) : MetaM Expr := do
  let u ← mkFreshLevelMVar
  let tya ← mkFreshExprMVar (mkSort u)
  let tyb ← mkFreshExprMVar (mkSort u)
  let heq := mkApp4 (mkConst ``HEq [u]) tya (← mkFreshExprMVar tya) tyb (← mkFreshExprMVar tyb)
  if let some expectedType := expectedType? then
    unless ← isDefEq expectedType heq do
      throwError m!"Type{indentD expectedType}\nis expected to be a `HEq`."
  return heq

def mkIffForExpectedType (expectedType? : Option Expr) : MetaM Expr := do
  let a ← mkFreshExprMVar (Expr.sort .zero)
  let b ← mkFreshExprMVar (Expr.sort .zero)
  let iff := mkApp2 (Expr.const `Iff []) a b
  if let some expectedType := expectedType? then
    unless ← isDefEq expectedType iff do
      throwError m!"Type{indentD expectedType}\nis expected to be an `Iff`."
  return iff

def ensureIff (pf : Expr) : MetaM Expr := do
  discard <| mkIffForExpectedType (← inferType pf)
  return pf

inductive CongrType
  | eq | heq

structure CongrResult where
  /-- The left-hand side of the congruence result. -/
  lhs : Expr
  /-- The right-hand side of the congruence result. -/
  rhs : Expr
  /-- A generator for an `Eq lhs rhs` or `HEq lhs rhs` proof.
  If such a proof is impossible, the generator can throw an error.
  The inferred type of the generated proof needs only be defeq to `Eq lhs rhs` or `HEq lhs rhs`.
  This function can assign metavariables when constructing the proof.

  If `pf? = none`, then `lhs` and `rhs` are defeq, and the proof is by reflexivity. -/
  (pf? : Option (CongrType → MetaM Expr))

def CongrResult.isRfl (res : CongrResult) : Bool := res.pf?.isNone

def CongrResult.eq (res : CongrResult) : MetaM Expr := do
  unless ← isDefEq (← inferType res.lhs) (← inferType res.rhs) do
    throwError "Expecting{indentD res.lhs}\nand{indentD res.rhs}\n\
      to have definitionally equal types."
  match res.pf? with
  | some pf => pf .eq
  | none => mkEqRefl res.lhs

def CongrResult.heq (res : CongrResult) : MetaM Expr := do
  match res.pf? with
  | some pf => pf .heq
  | none => mkHEqRefl res.lhs

def CongrResult.iff (res : CongrResult) : MetaM Expr := do
  unless ← Meta.isProp res.lhs do
    throwError "Expecting{indentD res.lhs}\nto be a proposition."
  return mkApp3 (.const ``iff_of_eq []) res.lhs res.rhs (← res.eq)

def CongrResult.trans (res1 res2 : CongrResult) : CongrResult where
  lhs := res1.lhs
  rhs := res2.rhs
  pf? :=
    if res1.isRfl then
      res2.pf?
    else if res2.isRfl then
      res1.pf?
    else
      some fun
        | .eq => do mkEqTrans (← res1.eq) (← res2.eq)
        | .heq => do mkHEqTrans (← res1.heq) (← res2.heq)

def CongrResult.mk' (lhs rhs : Expr) (pf : Expr) : CongrResult where
  lhs := lhs
  rhs := rhs
  pf? := some fun
    | .eq => do ensureSidesDefeq (← toEqPf)
    | .heq => do ensureSidesDefeq (← toHEqPf)
where
  /-- Given a `pf` of an `Iff`, `Eq`, or `HEq`, return a proof of `Eq`.
  If `pf` is not obviously any of these, weakly try inserting `propext` to make an `Iff`
  and otherwise unify the type with `Eq`. -/
  toEqPf : MetaM Expr := do
    let ty ← whnf (← inferType pf)
    if let some .. := ty.iff? then
      mkPropExt pf
    else if let some .. := ty.eq? then
      return pf
    else if let some (lhsTy, _, rhsTy, _) := ty.heq? then
      unless ← isDefEq lhsTy rhsTy do
        throwError "Cannot turn HEq proof into an equality proof. Has type{indentD ty}"
      mkAppM ``eq_of_heq #[pf]
    else if ← Meta.isProp lhs then
      mkPropExt (← ensureIff pf)
    else
      discard <| mkEqForExpectedType (← inferType pf)
      return pf
  /-- Given a `pf` of an `Iff`, `Eq`, or `HEq`, return a proof of `HEq`.
  If `pf` is not obviously any of these, weakly try making it be an `Eq` or an `Iff`,
  and otherwise make it be a `HEq`. -/
  toHEqPf : MetaM Expr := do
    let ty ← whnf (← inferType pf)
    if let some .. := ty.iff? then
      mkAppM ``heq_of_eq #[← mkPropExt pf]
    else if let some .. := ty.eq? then
      mkAppM ``heq_of_eq #[pf]
    else if let some .. := ty.heq? then
      return pf
    else if ← withNewMCtxDepth <| isDefEq (← inferType lhs) (← inferType rhs) then
      mkAppM ``heq_of_eq #[← toEqPf]
    else
      discard <| mkHEqForExpectedType (← inferType pf)
      return pf
  /-- Get the sides of the type of `pf` and unify them with the respective `lhs` and `rhs`. -/
  ensureSidesDefeq (pf : Expr) : MetaM Expr := do
    let pfTy ← inferType pf
    let some (_, lhs', _, rhs') := (← whnf pfTy).sides?
      | panic! "Unexpectedly did not generate an eq or heq"
    unless ← isDefEq lhs lhs' do
      throwError "Congruence hole has type{indentD pfTy}\n\
        but its left-hand side is not definitionally equal to the expected value{indentD lhs}"
    unless ← isDefEq rhs rhs' do
      throwError "Congruence hole has type{indentD pfTy}\n\
        but its right-hand side is not definitionally equal to the expected value{indentD rhs}"
    return pf

def CongrResult.defeq (res : CongrResult) : MetaM CongrResult := do
  if res.isRfl then
    return res
  else
    unless ← isDefEq res.lhs res.rhs do
      throwError "Cannot generate congruence because we need{indentD res.lhs}\n\
        to be definitionally equal to{indentD res.rhs}"
    -- Propagate types into any proofs that we're dropping:
    discard <| res.eq
    return {res with pf? := none}

def CongrResult.mkDefault (lhs rhs : Expr) : MetaM CongrResult := do
  if ← isDefEq lhs rhs then
    return {lhs, rhs, pf? := none}
  else if let some pf ← (observing? <| mkAppM ``Subsingleton.elim #[lhs, rhs]) then
    return CongrResult.mk' lhs rhs pf
  else if let some pf ← (observing? <| mkAppM ``proof_irrel_heq #[lhs, rhs]) then
    return CongrResult.mk' lhs rhs pf
  throwError "Could not generate congruence between{indentD lhs}\nand{indentD rhs}"

def CongrResult.mkDefault' (mvarCounterSaved : Nat) (lhs rhs : Expr) : MetaM CongrResult := do
  if let some h := hasCHole mvarCounterSaved lhs then
    throwError "Left-hand side{indentD lhs}\nstill has a congruence hole{indentD h}"
  if let some h := hasCHole mvarCounterSaved rhs then
    throwError "Right-hand side{indentD rhs}\nstill has a congruence hole{indentD h}"
  CongrResult.mkDefault lhs rhs

def throwCongrEx {α : Type} (lhs rhs : Expr) (msg : MessageData) : MetaM α := do
  throwError "congr(...) failed with left-hand side{indentD lhs}\n\
    and right-hand side {indentD rhs}\n{msg}"

def mkCongrOfCHole? (mvarCounterSaved : Nat) (lhs rhs : Expr) : MetaM (Option CongrResult) := do
  match cHole? lhs mvarCounterSaved, cHole? rhs mvarCounterSaved with
  | some (isLhs1, val1, pf1), some (isLhs2, val2, pf2) =>
    trace[Elab.congr] "mkCongrOfCHole, both holes"
    unless isLhs1 == true do
      throwCongrEx lhs rhs "A RHS congruence hole leaked into the LHS"
    unless isLhs2 == false do
      throwCongrEx lhs rhs "A LHS congruence hole leaked into the RHS"
    -- Defeq checks to unify the lhs and rhs congruence holes.
    unless ← isDefEq (← inferType pf1) (← inferType pf2) do
      throwCongrEx lhs rhs "Elaborated types of congruence holes are not defeq."
    if let some (_, lhsVal, _, rhsVal) := (← whnf <| ← inferType pf1).sides? then
      unless ← isDefEq val1 lhsVal do
        throwError "Left-hand side of congruence hole is{indentD lhsVal}\n\
          but is expected to be{indentD val1}"
      unless ← isDefEq val2 rhsVal do
        throwError "Right-hand side of congruence hole is{indentD rhsVal}\n\
          but is expected to be{indentD val2}"
    return some <| CongrResult.mk' val1 val2 pf1
  | some .., none =>
    throwCongrEx lhs rhs "Right-hand side lost its congruence hole annotation."
  | none, some .. =>
    throwCongrEx lhs rhs "Left-hand side lost its congruence hole annotation."
  | none, none => return none

partial def mkCongrOf (depth : Nat) (mvarCounterSaved : Nat) (lhs rhs : Expr) :
    MetaM CongrResult := do
  trace[Elab.congr] "mkCongrOf: {depth}, {lhs}, {rhs}, {(← mkFreshExprMVar none).mvarId!}"
  if depth > 1000 then
    throwError "congr(...) internal error: out of gas"
  -- Potentially metavariables get assigned as we process congruence holes,
  -- so instantiate them to be safe. Placeholders and implicit arguments might
  -- end up with congruence holes, so they indeed might need a nontrivial congruence.
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if let some res ← mkCongrOfCHole? mvarCounterSaved lhs rhs then
    trace[Elab.congr] "hole processing succeeded"
    return res
  if (hasCHole mvarCounterSaved lhs).isNone && (hasCHole mvarCounterSaved rhs).isNone then
    -- It's safe to fastforward if the lhs and rhs are defeq and have no congruence holes.
    -- This is more conservative than necessary since congruence holes might only be inside proofs.
    if ← isDefEq lhs rhs then
      return {lhs, rhs, pf? := none}
  if ← (isProof lhs <||> isProof rhs) then
    -- We don't want to look inside proofs at all.
    return ← CongrResult.mkDefault lhs rhs
  match lhs, rhs with
  | .app .., .app .. =>
    trace[Elab.congr] "app"
    let arity := lhs.getAppNumArgs
    unless arity == rhs.getAppNumArgs do
      trace[Elab.congr] "app desync (arity)"
      return ← CongrResult.mkDefault' mvarCounterSaved lhs rhs
    let f := lhs.getAppFn
    let f' := rhs.getAppFn
    unless ← isDefEq (← inferType f) (← inferType f') do
      trace[Elab.congr] "app desync (function types)"
      return ← CongrResult.mkDefault' mvarCounterSaved lhs rhs
    let fnRes ← mkCongrOf (depth + 1) mvarCounterSaved f f'
    trace[Elab.congr] "mkCongrOf functions {f}, {f'} has isRfl = {fnRes.isRfl}"
    if !fnRes.isRfl then
      -- If there's a nontrivial proof, then since mkHCongrWithArity fixes the function
      -- we need to handle this ourselves.
      let lhs := mkAppN fnRes.lhs lhs.getAppArgs
      let lhs' := mkAppN fnRes.rhs lhs.getAppArgs
      let rhs := mkAppN fnRes.rhs rhs.getAppArgs
      let mut pf ← fnRes.eq
      for arg in lhs.getAppArgs do
        pf ← mkCongrFun pf arg
      let res1 := CongrResult.mk' lhs lhs' pf
      let res2 ← mkCongrOf (depth + 1) mvarCounterSaved lhs' rhs
      return res1.trans res2
    let thm ← mkHCongrWithArity' fnRes.lhs arity
    let mut args := #[]
    let mut lhsArgs := #[]
    let mut rhsArgs := #[]
    let mut nontriv : Bool := false
    for lhs' in lhs.getAppArgs, rhs' in rhs.getAppArgs, kind in thm.argKinds do
      match kind with
      | .eq =>
        let res ← mkCongrOf (depth + 1) mvarCounterSaved lhs' rhs'
        nontriv := nontriv || !res.isRfl
        args := args |>.push res.lhs |>.push res.rhs |>.push (← res.eq)
        lhsArgs := lhsArgs.push res.lhs
        rhsArgs := rhsArgs.push res.rhs
      | .heq =>
        let res ← mkCongrOf (depth + 1) mvarCounterSaved lhs' rhs'
        nontriv := nontriv || !res.isRfl
        args := args |>.push res.lhs |>.push res.rhs |>.push (← res.heq)
        lhsArgs := lhsArgs.push res.lhs
        rhsArgs := rhsArgs.push res.rhs
      | .subsingletonInst =>
        -- Warning: we're not processing any congruence holes here.
        -- Users shouldn't be intentionally placing them in such arguments anyway.
        -- We can't throw an error because these arguments might incidentally have
        -- congruence holes by unification.
        nontriv := true
        let lhs := removeCHoles lhs'
        let rhs := removeCHoles rhs'
        args := args |>.push lhs |>.push rhs
        lhsArgs := lhsArgs.push lhs
        rhsArgs := rhsArgs.push rhs
      | _ => panic! "unexpected hcongr argument kind"
    let lhs := mkAppN fnRes.lhs lhsArgs
    let rhs := mkAppN fnRes.rhs rhsArgs
    if nontriv then
      return CongrResult.mk' lhs rhs (mkAppN thm.proof args)
    else
      -- `lhs` and `rhs` *should* be defeq, but use `mkDefault` just to be safe.
      CongrResult.mkDefault lhs rhs
  | .lam .., .lam .. =>
    trace[Elab.congr] "lam"
    let resDom ← mkCongrOf (depth + 1) mvarCounterSaved lhs.bindingDomain! rhs.bindingDomain!
    -- We do not yet support congruences in the binding domain for lambdas.
    discard <| resDom.defeq
    withLocalDecl lhs.bindingName! lhs.bindingInfo! resDom.lhs fun x => do
      let lhsb := lhs.bindingBody!.instantiate1 x
      let rhsb := rhs.bindingBody!.instantiate1 x
      let resBody ← mkCongrOf (depth + 1) mvarCounterSaved lhsb rhsb
      let lhs ← mkLambdaFVars #[x] resBody.lhs
      let rhs ← mkLambdaFVars #[x] resBody.rhs
      if resBody.isRfl then
        return {lhs, rhs, pf? := none}
      else
        let pf ← mkLambdaFVars #[x] (← resBody.eq)
        return CongrResult.mk' lhs rhs (← mkAppM ``funext #[pf])
  | .forallE .., .forallE .. =>
    trace[Elab.congr] "forallE"
    let resDom ← mkCongrOf (depth + 1) mvarCounterSaved lhs.bindingDomain! rhs.bindingDomain!
    if lhs.isArrow && rhs.isArrow then
      let resBody ← mkCongrOf (depth + 1) mvarCounterSaved lhs.bindingBody! rhs.bindingBody!
      let lhs := Expr.forallE lhs.bindingName! resDom.lhs resBody.lhs lhs.bindingInfo!
      let rhs := Expr.forallE rhs.bindingName! resDom.rhs resBody.rhs rhs.bindingInfo!
      if resDom.isRfl && resBody.isRfl then
        return {lhs, rhs, pf? := none}
      else
        return CongrResult.mk' lhs rhs (← mkImpCongr (← resDom.eq) (← resBody.eq))
    else
      -- We do not yet support congruences in the binding domain for dependent pi types.
      discard <| resDom.defeq
      withLocalDecl lhs.bindingName! lhs.bindingInfo! resDom.lhs fun x => do
        let lhsb := lhs.bindingBody!.instantiate1 x
        let rhsb := rhs.bindingBody!.instantiate1 x
        let resBody ← mkCongrOf (depth + 1) mvarCounterSaved lhsb rhsb
        let lhs ← mkForallFVars #[x] resBody.lhs
        let rhs ← mkForallFVars #[x] resBody.rhs
        if resBody.isRfl then
          return {lhs, rhs, pf? := none}
        else
          let pf ← mkLambdaFVars #[x] (← resBody.eq)
          return CongrResult.mk' lhs rhs (← mkAppM ``pi_congr #[pf])
  | .letE .., .letE .. =>
    trace[Elab.congr] "letE"
    -- Just zeta reduce for now. Could look at `Lean.Meta.Simp.simp.simpLet`
    let lhs := lhs.letBody!.instantiate1 lhs.letValue!
    let rhs := rhs.letBody!.instantiate1 rhs.letValue!
    mkCongrOf (depth + 1) mvarCounterSaved lhs rhs
  | .mdata _ lhs', .mdata _ rhs' =>
    trace[Elab.congr] "mdata"
    let res ← mkCongrOf (depth + 1) mvarCounterSaved lhs' rhs'
    return {res with lhs := lhs.updateMData! res.lhs, rhs := rhs.updateMData! res.rhs}
  | .proj n1 i1 e1, .proj n2 i2 e2 =>
    trace[Elab.congr] "proj"
    -- Only handles defeq at the moment.
    unless n1 == n2 && i1 == i2 do
      throwCongrEx lhs rhs "Incompatible primitive projections"
    let res ← mkCongrOf (depth + 1) mvarCounterSaved e1 e2
    discard <| res.defeq
    return {lhs := lhs.updateProj! res.lhs, rhs := rhs.updateProj! res.rhs, pf? := none}
  | _, _ =>
    trace[Elab.congr] "base case"
    CongrResult.mkDefault' mvarCounterSaved lhs rhs

/-! ### Elaborating congruence quotations -/

@[term_elab termCongr, inherit_doc termCongr]
def elabTermCongr : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(congr($t)) =>
    -- Save the current mvarCounter so that we know which cHoles are for this congr quotation.
    let mvarCounterSaved := (← getMCtx).mvarCounter
    -- Case 1: There is an expected type and it's obviously an Iff/Eq/HEq.
    if let some expectedType := expectedType? then
      if let some (expLhsTy, expLhs, expRhsTy, expRhs) := (← whnf expectedType).sides? then
        let lhs ← elaboratePattern t expLhsTy true
        let rhs ← elaboratePattern t expRhsTy false
        -- Note: these defeq checks can leak congruence holes.
        unless ← isDefEq expLhs lhs do
          throwError "Left-hand side of elaborated pattern{indentD lhs}\n\
            is not definitionally equal to left-hand side of expected type{indentD expectedType}"
        unless ← isDefEq expRhs rhs do
          throwError "Right-hand side of elaborated pattern{indentD rhs}\n\
            is not definitionally equal to right-hand side of expected type{indentD expectedType}"
        Term.synthesizeSyntheticMVars (postpone := .yes)
        let res ← mkCongrOf 0 mvarCounterSaved lhs rhs
        let expectedType' ← whnf expectedType
        let pf ← if expectedType'.iff?.isSome then res.iff
                  else if expectedType'.isEq then res.eq
                  else if expectedType'.isHEq then res.heq
                  else panic! "unreachable case, sides? guarantees Iff, Eq, and HEq"
        return ← mkExpectedTypeHint pf expectedType
    -- Case 2: No expected type or it's not obviously Iff/Eq/HEq. We generate an Eq.
    let lhs ← elaboratePattern t none true
    let rhs ← elaboratePattern t none false
    Term.synthesizeSyntheticMVars (postpone := .yes)
    let res ← mkCongrOf 0 mvarCounterSaved lhs rhs
    let pf ← res.eq
    let ty ← mkEq res.lhs res.rhs
    mkExpectedTypeHint pf ty
  | _ => throwUnsupportedSyntax

end TermCongr

end Mathlib.Tactic
