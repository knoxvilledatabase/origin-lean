/-
Extracted from Tactic/Linter/RefineLinter.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header

/-!
# The "refine" linter

The "refine" linter flags usages of the `refine'` tactic.

The tactics `refine` and `refine'` are similar, but they handle meta-variables slightly differently.
This means that they are not completely interchangeable, nor can one completely replace the other.
However, `refine` is more readable and (heuristically) tends to be more efficient on average.

This linter is an incentive to discourage uses of `refine'`, without being a ban.
-/

open Lean Elab

namespace Mathlib.Linter

register_option linter.refine : Bool := {

  defValue := false

  descr := "enable the refine linter"

}

partial

def getRefine' : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let rargs := (args.map getRefine').flatten
    if kind == ``Lean.Parser.Tactic.refine' then rargs.push stx else rargs
  | _ => default

@[inherit_doc linter.refine]
def refineLinter : Linter where run := withSetOptionIn fun _stx => do
  unless Linter.getLinterValue linter.refine (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for stx in (getRefine' _stx) do
    Linter.logLint linter.refine stx
      "The `refine'` tactic is discouraged: \
      please strongly consider using `refine` or `apply` instead."

initialize addLinter refineLinter

end Mathlib.Linter
