/-
Extracted from Util/ParseCommand.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Elab.Command
import Mathlib.Init

noncomputable section

/-!
# `#parse` -- a command to parse text and log outputs
-/

namespace Mathlib.GuardExceptions

open Lean Parser Elab Command

def captureException (env : Environment) (s : ParserFn) (input : String) : Except String Syntax :=
  let ictx := mkInputContext input "<input>"
  let s := s.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if !s.allErrors.isEmpty then
    .error (s.toErrorMsg ictx)
  else if ictx.input.atEnd s.pos then
    .ok s.stxStack.back
  else
    .error ((s.mkError "end of input").toErrorMsg ictx)

syntax (name := parseCmd) "#parse " ident " => " str : command

elab_rules : command

  | `(command| #parse $parserFnId => $str) => do

    elabCommand <| ← `(command|

      run_cmd do

        let exc ← Lean.ofExcept <| captureException (← getEnv) $parserFnId $str

        logInfo $str)

end Mathlib.GuardExceptions
