/-
Extracted from Data/MLList/IO.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Batteries.Data.MLList.Basic

noncomputable section

/-!
# Reading from handles, files, and processes as lazy lists.

## Deprecation

This material has been moved out of Mathlib to https://github.com/semorrison/lean-monadic-list.
-/

open System IO.FS

set_option linter.deprecated false

namespace MLList

def linesFromHandle (h : Handle) : MLList IO String :=
  MLList.iterate (do
    let line ← h.getLine
    -- This copies the logic from `IO.FS.lines`.
    if line.length == 0 then
      return none
    else if line.back == '\n' then
      let line := line.dropRight 1
      let line :=
        if System.Platform.isWindows && line.back == '\x0d' then line.dropRight 1 else line
      return some line
    else
      return some line)
  |>.takeWhile (·.isSome) |>.map (fun o => o.getD "")

def lines (f : FilePath) : MLList IO String := .squash fun _ => do
  return linesFromHandle (← Handle.mk f Mode.read)

open IO.Process in

def runCmd (cmd : String) (args : Array String) (input : String := "") : MLList IO String := do
  let child ← spawn
    { cmd := cmd, args := args, stdin := .piped, stdout := .piped, stderr := .piped }
  linesFromHandle (← put child input).stdout
where put
    (child : Child { stdin := .piped, stdout := .piped, stderr := .piped }) (input : String) :
    IO (Child { stdin := .null, stdout := .piped, stderr := .piped }) := do
  let (stdin, child) ← child.takeStdin
  stdin.putStr input
  stdin.flush
  return child

end MLList
