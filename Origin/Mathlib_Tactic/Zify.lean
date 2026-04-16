/-
Extracted from Tactic/Zify.lean
Genuine: 10 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Attr.Register
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Order.Basic

noncomputable section

/-!
# `zify` tactic

The `zify` tactic is used to shift propositions from `Nat` to `Int`.
This is often useful since `Int` has well-behaved subtraction.
```
example (a b c x y z : Nat) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  zify
  zify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
```
-/

namespace Mathlib.Tactic.Zify

open Lean

open Lean.Meta

open Lean.Parser.Tactic

open Lean.Elab.Tactic

syntax (name := zify) "zify" (simpArgs)? (location)? : tactic

macro_rules

| `(tactic| zify $[[$simpArgs,*]]? $[at $location]?) =>

  let args := simpArgs.map (·.getElems) |>.getD #[]

  `(tactic|

    simp -decide only [zify_simps, push_cast, $args,*] $[at $location]?)

def mkZifyContext (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ",")) :
    TacticM MkSimpContextResult := do
  let args := simpArgs.map (·.getElems) |>.getD #[]
  mkSimpContext
    (← `(tactic| simp -decide only [zify_simps, push_cast, $args,*])) false

def applySimpResultToProp' (proof : Expr) (prop : Expr) (r : Simp.Result) : MetaM (Expr × Expr) :=
  do
  match r.proof? with
  | some eqProof => return (← mkExpectedTypeHint (← mkEqMP eqProof proof) r.expr, r.expr)
  | none =>
    if r.expr != prop then
      return (← mkExpectedTypeHint proof r.expr, r.expr)
    else
      return (proof, r.expr)

def zifyProof (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ","))
    (proof : Expr) (prop : Expr) : TacticM (Expr × Expr) := do
  let ctx_result ← mkZifyContext simpArgs
  let (r, _) ← simp prop ctx_result.ctx
  applySimpResultToProp' proof prop r

@[zify_simps] lemma natCast_eq (a b : Nat) : a = b ↔ (a : Int) = (b : Int) := Int.ofNat_inj.symm

@[zify_simps] lemma natCast_le (a b : Nat) : a ≤ b ↔ (a : Int) ≤ (b : Int) := Int.ofNat_le.symm

@[zify_simps] lemma natCast_lt (a b : Nat) : a < b ↔ (a : Int) < (b : Int) := Int.ofNat_lt.symm

@[zify_simps] lemma natCast_ne (a b : Nat) : a ≠ b ↔ (a : Int) ≠ (b : Int) :=
  not_congr Int.ofNat_inj.symm

@[zify_simps] lemma natCast_dvd (a b : Nat) : a ∣ b ↔ (a : Int) ∣ (b : Int) := Int.ofNat_dvd.symm

alias nat_cast_dvd := natCast_dvd

variable {R : Type*} [AddGroupWithOne R]

@[norm_cast] theorem Nat.cast_sub_of_add_le {m n k} (h : m + k ≤ n) :
    ((n - m : ℕ) : R) = n - m := Nat.cast_sub (m.le_add_right k |>.trans h)

@[norm_cast] theorem Nat.cast_sub_of_lt {m n} (h : m < n) :
    ((n - m : ℕ) : R) = n - m := Nat.cast_sub h.le

end Zify

end Mathlib.Tactic
