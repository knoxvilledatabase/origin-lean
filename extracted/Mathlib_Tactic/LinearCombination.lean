/-
Extracted from Tactic/LinearCombination.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Compare

noncomputable section

/-!
# linear_combination Tactic

In this file, the `linear_combination` tactic is created.  This tactic, which
works over `CommRing`s, attempts to simplify the target by creating a linear combination
of a list of equalities and subtracting it from the target. A `Syntax.Tactic`
object can also be passed into the tactic, allowing the user to specify a
normalization tactic.

Over ordered algebraic objects (such as `LinearOrderedCommRing`), taking linear combinations of
inequalities is also supported.

## Implementation Notes

This tactic works by creating a weighted sum of the given equations with the
given coefficients.  Then, it subtracts the right side of the weighted sum
from the left side so that the right side equals 0, and it does the same with
the target.  Afterwards, it sets the goal to be the equality between the
lefthand side of the new goal and the lefthand side of the new weighted sum.
Lastly, calls a normalization tactic on this target.

## References

* <https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/Linear.20algebra.20tactic/near/213928196>

-/

namespace Mathlib.Tactic.LinearCombination

open Lean hiding Rat

open Elab Meta Term Mathlib Ineq

inductive Expanded
  /-- A proof of `a = b`, `a ≤ b`, or `a < b` (according to the value of `Ineq`). -/
  | proof (rel : Ineq) (pf : Syntax.Term)
  /-- A value, equivalently a proof of `c = c`. -/
  | const (c : Syntax.Term)

def rescale (lems : Ineq.WithStrictness → Name) (ty : Option Expr) (p c : Term) :
    Ineq → TermElabM Expanded
  | eq => do
    let i := mkIdent <| lems .eq
    .proof eq <$> ``($i $p $c)
  | le => do
    let i := mkIdent <| lems .le
    let e₂ ← withSynthesizeLight <| Term.elabTerm c ty
    let hc₂ ← Meta.Positivity.proveNonneg e₂
    .proof le <$> ``($i $p $(← hc₂.toSyntax))
  | lt => do
    let e₂ ← withSynthesizeLight <| Term.elabTerm c ty
    let (strict, hc₂) ← Meta.Positivity.bestResult e₂
    let i := mkIdent <| lems (.lt strict)
    let p' : Term ← ``($i $p $(← hc₂.toSyntax))
    if strict then pure (.proof lt p') else pure (.proof le p')

partial def expandLinearCombo (ty : Option Expr) (stx : Syntax.Term) :
    TermElabM Expanded := withRef stx do
  match stx with
  | `(($e)) => expandLinearCombo ty e
  | `($e₁ + $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ + $c₂)
    | .proof rel₁ p₁, .proof rel₂ p₂ =>
      let i := mkIdent <| Ineq.addRelRelData rel₁ rel₂
      .proof (max rel₁ rel₂) <$> ``($i $p₁ $p₂)
    | .proof rel p, .const c | .const c, .proof rel p =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      pure (.proof rel p)
  | `($e₁ - $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ - $c₂)
    | .proof rel p, .const c =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      pure (.proof rel p)
    | .const c, .proof eq p =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      .proof eq <$> ``(Eq.symm $p)
    | .proof rel₁ p₁, .proof eq p₂ =>
      let i := mkIdent <| Ineq.addRelRelData rel₁ eq
      .proof rel₁ <$> ``($i $p₁ (Eq.symm $p₂))
    | _, .proof _ _ =>
      throwError "coefficients of inequalities in 'linear_combination' must be nonnegative"
  | `(-$e) => do
      match ← expandLinearCombo ty e with
      | .const c => .const <$> `(-$c)
      | .proof eq p => .proof eq <$> ``(Eq.symm $p)
      | .proof _ _ =>
        throwError "coefficients of inequalities in 'linear_combination' must be nonnegative"
  | `($e₁ *%$tk $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ * $c₂)
    | .proof rel₁ p₁, .const c₂ => rescale mulRelConstData ty p₁ c₂ rel₁
    | .const c₁, .proof rel₂ p₂ => rescale mulConstRelData ty p₂ c₁ rel₂
    | .proof _ _, .proof _ _ =>
      throwErrorAt tk "'linear_combination' supports only linear operations"
  | `($e₁ •%$tk $e₂) => do
    match ← expandLinearCombo none e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ • $c₂)
    | .proof rel₁ p₁, .const c₂ => rescale smulRelConstData ty p₁ c₂ rel₁
    | .const c₁, .proof rel₂ p₂ => rescale smulConstRelData none p₂ c₁ rel₂
    | .proof _ _, .proof _ _ =>
      throwErrorAt tk "'linear_combination' supports only linear operations"
  | `($e₁ /%$tk $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ / $c₂)
    | .proof rel₁ p₁, .const c₂ => rescale divRelConstData ty p₁ c₂ rel₁
    | _, .proof _ _ => throwErrorAt tk "'linear_combination' supports only linear operations"
  | e =>
    -- We have the expected type from the goal, so we can fully synthesize this leaf node.
    withSynthesize do
      -- It is OK to use `ty` as the expected type even if `e` is a proof.
      -- The expected type is just a hint.
      let c ← withSynthesizeLight <| Term.elabTerm e ty
      match ← try? (← inferType c).ineq? with
      | some (rel, _) => .proof rel <$> c.toSyntax
      | none => .const <$> c.toSyntax

def elabLinearCombination (tk : Syntax)
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term) :
    Tactic.TacticM Unit := Tactic.withMainContext <| Tactic.focus do
  let eType ← withReducible <| (← Tactic.getMainGoal).getType'
  let (goalRel, ty, _) ← eType.ineq?
  -- build the specified linear combination of the hypotheses
  let (hypRel, p) ← match input with
  | none => Prod.mk eq <$>  `(Eq.refl 0)
  | some e =>
    match ← expandLinearCombo ty e with
    | .const c =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      Prod.mk eq <$> `(Eq.refl 0)
    | .proof hypRel p => pure (hypRel, p)
  -- look up the lemma for the central `refine` in `linear_combination`
  let (reduceLem, newGoalRel) : Name × Ineq := ← do
    match Ineq.relImpRelData hypRel goalRel with
    | none => throwError "cannot prove an equality from inequality hypotheses"
    | some n => pure n
  -- build the term for the central `refine` in `linear_combination`
  let p' ← do
    match exp? with
    | some n =>
      if n.getNat = 1 then
        `($(mkIdent reduceLem) $p ?a)
      else
        match hypRel with
        | eq => `(eq_of_add_pow $n $p ?a)
        | _ => throwError
          "linear_combination tactic not implemented for exponentiation of inequality goals"
    | _ => `($(mkIdent reduceLem) $p ?a)
  -- run the central `refine` in `linear_combination`
  Term.withoutErrToSorry <| Tactic.refineCore p' `refine false
  -- if we are in a "true" ring, with well-behaved negation, we rearrange from the form
  -- `[stuff] = [stuff]` (or `≤` or `<`) to the form `[stuff] = 0` (or `≤` or `<`), because this
  -- gives more useful error messages on failure
  let _ ← Tactic.tryTactic <| Tactic.liftMetaTactic fun g ↦ g.applyConst newGoalRel.rearrangeData
  match norm? with
  -- now run the normalization tactic provided
  | some norm => Tactic.evalTactic norm
  -- or the default normalization tactic if none is provided
  | none => withRef tk <| Tactic.liftMetaFinishingTactic <|
    match newGoalRel with
    -- for an equality task the default normalization tactic is (the internals of) `ring1` (but we
    -- use `.instances` transparency, which is arguably more robust in algebraic settings than the
    -- choice `.reducible` made in `ring1`)
    | eq => fun g ↦ AtomM.run .instances <| Ring.proveEq g
    | le => Ring.proveLE
    | lt => Ring.proveLT

syntax normStx := atomic(" (" &"norm" " := ") withoutPosition(tactic) ")"

syntax expStx := atomic(" (" &"exp" " := ") withoutPosition(num) ")"

syntax (name := linearCombination) "linear_combination"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic

elab_rules : tactic

  | `(tactic| linear_combination%$tk $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>

    elabLinearCombination tk tac n e

end Mathlib.Tactic.LinearCombination
