/-
Extracted from Tactic/Linter/AdmitLinter.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Elab.Command
import Mathlib.Init

/-!
# The "admit" linter

The "admit" linter flags usages of the `admit` tactic.

The tactics `admit` and `sorry` are synonyms.
The use of `sorry` is much more common and should be preferred.

This linter is an incentive to discourage uses of `admit`, without being a ban.
-/

namespace Mathlib.Linter

register_option linter.admit : Bool := {

  defValue := false

  descr := "enable the admit linter"

}

namespace AdmitLinter

open Lean Elab

partial

def getAdmit (stx : Syntax) : Array Syntax :=
  if let `(tactic| admit) := stx then
    #[stx]
  else
    stx.foldArgs (fun arg r => r ++ getAdmit arg) #[]

def admitLinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.admit (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for stxAdmit in (getAdmit stx) do
    Linter.logLint linter.admit stxAdmit
      "The `admit` tactic is discouraged: please consider using the synonymous `sorry` instead."

initialize addLinter admitLinter

end AdmitLinter

end Mathlib.Linter
