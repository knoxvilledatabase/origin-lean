/-
Extracted from Tactic/LinearCombination'.lean
Genuine: 20 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.Ring

noncomputable section

/-!
# linear_combination' Tactic

In this file, the `linear_combination'` tactic is created.  This tactic, which
works over `CommRing`s, attempts to simplify the target by creating a linear combination
of a list of equalities and subtracting it from the target. A `Syntax.Tactic`
object can also be passed into the tactic, allowing the user to specify a
normalization tactic.

## Implementation Notes

This tactic works by creating a weighted sum of the given equations with the
given coefficients.  Then, it subtracts the right side of the weighted sum
from the left side so that the right side equals 0, and it does the same with
the target.  Afterwards, it sets the goal to be the equality between the
lefthand side of the new goal and the lefthand side of the new weighted sum.
Lastly, calls a normalization tactic on this target.

This file contains the `linear_combination'` tactic (note the '): the original
Lean 4 implementation of the "linear combination" idea, written at the time of
the port from Lean 3.  Notably, its scope includes certain *nonlinear*
operations.  The `linear_combination` tactic (in a separate file) is a variant
implementation, but this version is provided for backward-compatibility.

## References

* <https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/Linear.20algebra.20tactic/near/213928196>

-/

namespace Mathlib.Tactic.LinearCombination'

open Lean hiding Rat

open Elab Meta Term

variable {α : Type*} {a a' a₁ a₂ b b' b₁ b₂ c : α}

theorem pf_add_c [Add α] (p : a = b) (c : α) : a + c = b + c := p ▸ rfl

theorem c_add_pf [Add α] (p : b = c) (a : α) : a + b = a + c := p ▸ rfl

theorem add_pf [Add α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl

theorem pf_sub_c [Sub α] (p : a = b) (c : α) : a - c = b - c := p ▸ rfl

theorem c_sub_pf [Sub α] (p : b = c) (a : α) : a - b = a - c := p ▸ rfl

theorem sub_pf [Sub α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ - a₂ = b₁ - b₂ := p₁ ▸ p₂ ▸ rfl

theorem neg_pf [Neg α] (p : (a:α) = b) : -a = -b := p ▸ rfl

theorem pf_mul_c [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl

theorem c_mul_pf [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl

theorem mul_pf [Mul α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ * a₂ = b₁ * b₂ := p₁ ▸ p₂ ▸ rfl

theorem inv_pf [Inv α] (p : (a:α) = b) : a⁻¹ = b⁻¹ := p ▸ rfl

theorem pf_div_c [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl

theorem c_div_pf [Div α] (p : b = c) (a : α) : a / b = a / c := p ▸ rfl

theorem div_pf [Div α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ / a₂ = b₁ / b₂ := p₁ ▸ p₂ ▸ rfl

inductive Expanded
  /-- A proof of `a = b`. -/
  | proof (pf : Syntax.Term)
  /-- A value, equivalently a proof of `c = c`. -/
  | const (c : Syntax.Term)

partial def expandLinearCombo (ty : Expr) (stx : Syntax.Term) : TermElabM Expanded := withRef stx do
  match stx with
  | `(($e)) => expandLinearCombo ty e
  | `($e₁ + $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ + $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_add_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_add_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(add_pf $p₁ $p₂)
  | `($e₁ - $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ - $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_sub_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_sub_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(sub_pf $p₁ $p₂)
  | `(-$e) => do
    match ← expandLinearCombo ty e with
    | .const c => .const <$> `(-$c)
    | .proof p => .proof <$> ``(neg_pf $p)
  | `(← $e) => do
    match ← expandLinearCombo ty e with
    | .const c => return .const c
    | .proof p => .proof <$> ``(Eq.symm $p)
  | `($e₁ * $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ * $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_mul_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_mul_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(mul_pf $p₁ $p₂)
  | `($e⁻¹) => do
    match ← expandLinearCombo ty e with
    | .const c => .const <$> `($c⁻¹)
    | .proof p => .proof <$> ``(inv_pf $p)
  | `($e₁ / $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ / $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_div_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_div_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(div_pf $p₁ $p₂)
  | e =>
    -- We have the expected type from the goal, so we can fully synthesize this leaf node.
    withSynthesize do
      -- It is OK to use `ty` as the expected type even if `e` is a proof.
      -- The expected type is just a hint.
      let c ← withSynthesizeLight <| Term.elabTerm e ty
      if (← whnfR (← inferType c)).isEq then
        .proof <$> c.toSyntax
      else
        .const <$> c.toSyntax

theorem eq_trans₃ (p : (a:α) = b) (p₁ : a = a') (p₂ : b = b') : a' = b' := p₁ ▸ p₂ ▸ p

theorem eq_of_add [AddGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; rwa [sub_eq_zero, p] at H

theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : ℕ) (p : (a:α) = b)
    (H : (a' - b')^n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

def elabLinearCombination' (tk : Syntax)
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term)
    (twoGoals := false) : Tactic.TacticM Unit := Tactic.withMainContext do
  let some (ty, _) := (← (← Tactic.getMainGoal).getType').eq? |
    throwError "'linear_combination'' only proves equalities"
  let p ← match input with
  | none => `(Eq.refl 0)
  | some e =>
    match ← expandLinearCombo ty e with
    | .const c => `(Eq.refl $c)
    | .proof p => pure p
  let norm := norm?.getD (Unhygienic.run <| withRef tk `(tactic| ring1))
  Term.withoutErrToSorry <| Tactic.evalTactic <| ← withFreshMacroScope <|
  if twoGoals then
    `(tactic| (
      refine eq_trans₃ $p ?a ?b
      case' a => $norm:tactic
      case' b => $norm:tactic))
  else
    match exp? with
    | some n =>
      if n.getNat = 1 then `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))
      else `(tactic| (refine eq_of_add_pow $n $p ?a; case' a => $norm:tactic))
    | _ => `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))

syntax normStx := atomic(" (" &"norm" " := ") withoutPosition(tactic) ")"

syntax expStx := atomic(" (" &"exp" " := ") withoutPosition(num) ")"

syntax (name := linearCombination') "linear_combination'"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic

elab_rules : tactic

  | `(tactic| linear_combination'%$tk $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>

    elabLinearCombination' tk tac n e

syntax "linear_combination2" (normStx)? (ppSpace colGt term)? : tactic

elab_rules : tactic

  | `(tactic| linear_combination2%$tk $[(norm := $tac)]? $(e)?) =>

    elabLinearCombination' tk tac none e true

end Mathlib.Tactic.LinearCombination'
