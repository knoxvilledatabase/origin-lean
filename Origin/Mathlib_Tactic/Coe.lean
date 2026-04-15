/-
Extracted from Tactic/Coe.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Elab.ElabRules

/-!
# Additional coercion notation

Defines notation for coercions.
1. `↑ t` is defined in core.
2. `(↑)` is equivalent to the eta-reduction of `(↑ ·)`
3. `⇑ t` is a coercion to a function type.
4. `(⇑)` is equivalent to the eta-reduction of `(⇑ ·)`
3. `↥ t` is a coercion to a type.
6. `(↥)` is equivalent to the eta-reduction of `(↥ ·)`
-/

open Lean Meta

namespace Lean.Elab.Term.CoeImpl

def elabPartiallyAppliedCoe (sym : String) (expectedType : Expr)
    (mkCoe : (expectedType x : Expr) → TermElabM Expr) : TermElabM Expr := do
  let expectedType ← instantiateMVars expectedType
  let Expr.forallE _ a b .. := expectedType | do
    tryPostpone
    throwError "({sym}) must have a function type, not{indentExpr expectedType}"
  if b.hasLooseBVars then
    tryPostpone
    throwError "({sym}) must have a non-dependent function type, not{indentExpr expectedType}"
  if a.hasExprMVar then tryPostpone
  let f ← withLocalDeclD `x a fun x ↦ do
    mkLambdaFVars #[x] (← mkCoe b x)
  return f.etaExpanded?.getD f

elab "(" "↑" ")" : term <= expectedType =>

  elabPartiallyAppliedCoe "↑" expectedType fun b x => do

    if b.hasExprMVar then tryPostpone

    if let .some e ← coerce? x b then

      return e

    else

      throwError "cannot coerce{indentExpr x}\nto type{indentExpr b}"

elab "(" "⇑" ")" : term <= expectedType =>

  elabPartiallyAppliedCoe "⇑" expectedType fun b x => do

    if let some ty ← coerceToFunction? x then

      ensureHasType b ty

    else

      throwError "cannot coerce to function{indentExpr x}"

elab "(" "↥" ")" : term <= expectedType =>

  elabPartiallyAppliedCoe "↥" expectedType fun b x => do

    if let some ty ← coerceToSort? x then

      ensureHasType b ty

    else

      throwError "cannot coerce to sort{indentExpr x}"

end Lean.Elab.Term.CoeImpl
