/-
Extracted from Tactic/Eval.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Qq.Macro

/-!
# The `eval%` term elaborator

This file provides the `eval% x` term elaborator, which evaluates the constant `x` at compile-time
in the interpreter, and interpolates it into the expression.
-/

open Qq Lean Elab Term

namespace Mathlib.Meta

syntax (name := eval_expr) "eval% " term : term

@[term_elab eval_expr, inherit_doc eval_expr]
unsafe def elabEvalExpr : Lean.Elab.Term.TermElab
| `(term| eval% $stx) => fun exp => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize stx exp
  let e ← instantiateMVars e
  let ee ← Meta.mkAppM ``Lean.toExpr #[e]
  Lean.Meta.evalExpr Expr q(Expr) ee (safety := .unsafe)
| _ => fun _ => Elab.throwUnsupportedSyntax

end Mathlib.Meta
