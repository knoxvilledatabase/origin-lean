/-
Extracted from Tactic/Linter/HashCommandLinter.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header

/-!
# `#`-command linter

The `#`-command linter produces a warning when a command starting with `#` is used *and*
* either the command emits no message;
* or `warningAsError` is set to `true`.

The rationale behind this is that `#`-commands are intended to be transient:
they provide useful information in development, but are not intended to be present in final code.
Most of them are noisy and get picked up anyway by CI, but even the quiet ones are not expected to
outlive their in-development status.
-/

namespace Mathlib.Linter

register_option linter.hashCommand : Bool := {

  defValue := false

  descr := "enable the `#`-command linter"

}

namespace HashCommandLinter

open Lean Elab

open Command in

private partial def withSetOptionIn' (cmd : CommandElab) : CommandElab := fun stx => do
  if stx.getKind == ``Lean.Parser.Command.in then
    if stx[0].getKind == ``Lean.Parser.Command.set_option then
      let opts ← Elab.elabSetOption stx[0][1] stx[0][3]
      withScope (fun scope => { scope with opts }) do
        withSetOptionIn' cmd stx[2]
    else
      withSetOptionIn' cmd stx[2]
  else
    cmd stx

private abbrev allowed_commands : Std.HashSet String := { "#adaptation_note" }

def hashCommandLinter : Linter where run := withSetOptionIn' fun stx => do
  let mod := (← getMainModule).components
  if Linter.getLinterValue linter.hashCommand (← getOptions) &&
    ((← get).messages.toList.isEmpty || warningAsError.get (← getOptions)) &&
    -- we check that the module is either not in `test` or, is `test.HashCommandLinter`
    (mod.getD 0 default != `test || (mod == [`test, `HashCommandLinter]))
    then
    if let some sa := stx.getHead? then
      let a := sa.getAtomVal
      if (a.get ⟨0⟩ == '#' && ! allowed_commands.contains a) then
        let msg := m!"`#`-commands, such as '{a}', are not allowed in 'Mathlib'"
        if warningAsError.get (← getOptions) then
          logInfoAt sa (msg ++ " [linter.hashCommand]")
        else Linter.logLint linter.hashCommand sa msg

initialize addLinter hashCommandLinter

end HashCommandLinter
