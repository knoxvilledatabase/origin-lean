/-
Extracted from Tactic/Ring/RingNF.lean
Genuine: 15 | Conflates: 0 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.TryThis
import Mathlib.Tactic.Conv
import Mathlib.Util.Qq

/-!
# `ring_nf` tactic

A tactic which uses `ring` to rewrite expressions. This can be used non-terminally to normalize
ring expressions in the goal such as `⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to
prove some equations that `ring` cannot because they involve ring reasoning inside a subterm,
such as `sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

-/

namespace Mathlib.Tactic

open Lean hiding Rat

open Qq Meta

namespace Ring

variable {u : Level} {arg : Q(Type u)} {sα : Q(CommSemiring $arg)} {a : Q($arg)}

def ExBase.isAtom : ExBase sα a → Bool
  | .atom _ => true
  | _ => false

def ExProd.isAtom : ExProd sα a → Bool
  | .mul va₁ (.const 1 _) (.const 1 _) => va₁.isAtom
  | _ => false

def ExSum.isAtom : ExSum sα a → Bool
  | .add va₁ va₂ => match va₂ with -- FIXME: this takes a while to compile as one match
    | .zero => va₁.isAtom
    | _ => false
  | _ => false

end Ring

namespace RingNF

open Ring

inductive RingMode where
  /-- Sum-of-products form, like `x + x * y * 2 + z ^ 2`. -/
  | SOP
  /-- Raw form: the representation `ring` uses internally. -/
  | raw
  deriving Inhabited, BEq, Repr

structure Config where
  /-- the reducibility setting to use when comparing atoms for defeq -/
  red := TransparencyMode.reducible
  /-- if true, atoms inside ring expressions will be reduced recursively -/
  recursive := true
  /-- The normalization style. -/
  mode := RingMode.SOP
  deriving Inhabited, BEq, Repr

declare_config_elab elabConfig Config

structure Context where
  /-- A basically empty simp context, passed to the `simp` traversal in `RingNF.rewrite`. -/
  ctx : Simp.Context
  /-- A cleanup routine, which simplifies normalized polynomials to a more human-friendly
  format. -/
  simp : Simp.Result → SimpM Simp.Result

abbrev M := ReaderT Context AtomM

def rewrite (parent : Expr) (root := true) : M Simp.Result :=
  fun nctx rctx s ↦ do
    let pre : Simp.Simproc := fun e =>
      try
        guard <| root || parent != e -- recursion guard
        let e ← withReducible <| whnf e
        guard e.isApp -- all interesting ring expressions are applications
        let ⟨u, α, e⟩ ← inferTypeQ' e
        let sα ← synthInstanceQ (q(CommSemiring $α) : Q(Type u))
        let c ← mkCache sα
        let ⟨a, _, pa⟩ ← match ← isAtomOrDerivable sα c e rctx s with
        | none => eval sα c e rctx s -- `none` indicates that `eval` will find something algebraic.
        | some none => failure -- No point rewriting atoms
        | some (some r) => pure r -- Nothing algebraic for `eval` to use, but `norm_num` simplifies.
        let r ← nctx.simp { expr := a, proof? := pa }
        if ← withReducible <| isDefEq r.expr e then return .done { expr := r.expr }
        pure (.done r)
      catch _ => pure <| .continue
    let post := Simp.postDefault #[]
    (·.1) <$> Simp.main parent nctx.ctx (methods := { pre, post })

variable {R : Type*} [CommSemiring R] {n d : ℕ}

theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm

theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm

theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp

theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm

theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp

theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp

theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl

theorem int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp

theorem rat_rawCast_pos {R} [DivisionRing R] :
    (Rat.rawCast (.ofNat n) d : R) = Nat.rawCast n / Nat.rawCast d := by simp

theorem rat_rawCast_neg {R} [DivisionRing R] :
    (Rat.rawCast (.negOfNat n) d : R) = Int.rawCast (.negOfNat n) / Nat.rawCast d := by simp

partial def M.run
    {α : Type} (s : IO.Ref AtomM.State) (cfg : RingNF.Config) (x : M α) : MetaM α := do
  let ctx := {
    simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}]
    congrTheorems := ← getSimpCongrTheorems
    config.singlePass := cfg.mode matches .raw }
  let simp ← match cfg.mode with
  | .raw => pure pure
  | .SOP =>
    let thms : SimpTheorems := {}
    let thms ← [``add_zero, ``add_assoc_rev, ``_root_.mul_one, ``mul_assoc_rev,
      ``_root_.pow_one, ``mul_neg, ``add_neg].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
      ``rat_rawCast_neg, ``rat_rawCast_pos].foldlM (·.addConst · (post := false)) thms
    let ctx' := { ctx with simpTheorems := #[thms] }
    pure fun r' : Simp.Result ↦ do
      r'.mkEqTrans (← Simp.main r'.expr ctx' (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1
  let nctx := { ctx, simp }
  let rec
    /-- The recursive context. -/
    rctx := { red := cfg.red, evalAtom },
    /-- The atom evaluator calls either `RingNF.rewrite` recursively,
    or nothing depending on `cfg.recursive`. -/
    evalAtom := if cfg.recursive
      then fun e ↦ rewrite e false nctx rctx s
      else fun e ↦ pure { expr := e }
  x nctx rctx s

initialize ringCleanupRef.set fun e => do

  M.run (← IO.mkRef {}) { recursive := false } fun nctx _ _ =>

    return (← nctx.simp { expr := e } ({} : Lean.Meta.Simp.Methods).toMethodsRef nctx.ctx

      |>.run {}).1.expr

open Elab.Tactic Parser.Tactic

def ringNFTarget (s : IO.Ref AtomM.State) (cfg : Config) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let r ← M.run s cfg <| rewrite tgt
  if r.expr.consumeMData.isConstOf ``True then
    goal.assign (← mkOfEqTrue (← r.getProof))
    replaceMainGoal []
  else
    replaceMainGoal [← applySimpResultToTarget goal tgt r]

def ringNFLocalDecl (s : IO.Ref AtomM.State) (cfg : Config) (fvarId : FVarId) :
    TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← fvarId.getType)
  let goal ← getMainGoal
  let myres ← M.run s cfg <| rewrite tgt
  match ← applySimpResultToLocalDecl goal fvarId myres false with
  | none => replaceMainGoal []
  | some (_, newGoal) => replaceMainGoal [newGoal]

elab (name := ringNF) "ring_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do

  let mut cfg ← elabConfig cfg

  if tk.isSome then cfg := { cfg with red := .default }

  let loc := (loc.map expandLocation).getD (.targets #[] true)

  let s ← IO.mkRef {}

  withLocation loc (ringNFLocalDecl s cfg) (ringNFTarget s cfg)

    fun _ ↦ throwError "ring_nf failed"

  `(tactic| ring_nf ! $cfg:optConfig $(loc)?)

elab (name := ring1NF) "ring1_nf" tk:"!"? cfg:optConfig : tactic => do

  let mut cfg ← elabConfig cfg

  if tk.isSome then cfg := { cfg with red := .default }

  let s ← IO.mkRef {}

  liftMetaMAtMain fun g ↦ M.run s cfg <| proveEq g

  `(tactic| ring1_nf ! $cfg:optConfig)

@[inherit_doc ring1NF] macro "ring1_nf!" cfg:optConfig : tactic =>
@[tactic ringNFConv] def elabRingNFConv : Tactic := fun stx ↦ match stx with
  | `(conv| ring_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabConfig cfg
    if tk.isSome then cfg := { cfg with red := .default }
    let s ← IO.mkRef {}
    Conv.applySimpResult (← M.run s cfg <| rewrite (← instantiateMVars (← Conv.getLhs)))
  | _ => Elab.throwUnsupportedSyntax

  `(conv| ring_nf ! $cfg:optConfig)

macro (name := ring) "ring" : tactic =>

  `(tactic| first | ring1 | try_this ring_nf)

  `(tactic| first | ring1! | try_this ring_nf!)

macro (name := ringConv) "ring" : conv =>

  `(conv| first | discharge => ring1 | try_this ring_nf)

  `(conv| first | discharge => ring1! | try_this ring_nf!)

end RingNF

end Mathlib.Tactic
