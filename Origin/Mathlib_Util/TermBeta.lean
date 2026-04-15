/-
Extracted from Util/TermBeta.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Elab.Term

/-! `beta%` term elaborator

The `beta% f x1 ... xn` term elaborator elaborates the expression
`f x1 ... xn` and then does one level of beta reduction.
That is, if `f` is a lambda then it will substitute its arguments.

The purpose of this is to support substitutions in notations such as
`∀ i, beta% p i` so that `p i` gets beta reduced when `p` is a lambda.
-/

namespace Mathlib.Util.TermBeta

open Lean Elab Term

syntax (name := betaStx) "beta% " term : term

@[term_elab betaStx, inherit_doc betaStx]
def elabBeta : TermElab := fun stx expectedType? =>
  match stx with
  | `(beta% $t) => do
    let e ← elabTerm t expectedType?
    return (← instantiateMVars e).headBeta
  | _ => throwUnsupportedSyntax

end Mathlib.Util.TermBeta
