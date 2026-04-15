/-
Extracted from Tactic/Linter/TextBased.lean
Genuine: 20 of 20 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Batteries.Data.String.Matcher
import Mathlib.Data.Nat.Notation

/-!
## Text-based linters

This file defines various mathlib linters which are based on reading the source code only.
In practice, all such linters check for code style issues.

For now, this only contains linters checking
- that the copyright header and authors line are correctly formatted
- existence of module docstrings (in the right place)
- for certain disallowed imports
- if the string "adaptation note" is used instead of the command #adaptation_note
- files are at most 1500 lines long (unless specifically allowed).

For historic reasons, some of these checks are still written in a Python script `lint-style.py`:
these are gradually being rewritten in Lean.

This linter maintains a list of exceptions, for legacy reasons.
Ideally, the length of the list of exceptions tends to 0.

The `longFile` and the `longLine` *syntax* linter take care of flagging lines that exceed the
100 character limit and files that exceed the 1500 line limit.
The text-based versions of this file are still used for the files where the linter is not imported.
This means that the exceptions for the text-based linters are shorter, as they do not need to
include those handled with `set_option linter.style.longFile x`/`set_option linter.longLine false`.

An executable running all these linters is defined in `scripts/lint-style.lean`.
-/

open System

namespace Mathlib.Linter.TextBased

inductive BroadImports
  /-- Importing the entire "Mathlib.Tactic" folder -/
  | TacticFolder
  /-- Importing any module in `Lake`, unless carefully measured
  This has caused unexpected regressions in the past. -/
  | Lake

deriving BEq

inductive StyleError where
  /-- The bare string "Adaptation note" (or variants thereof): instead, the
  #adaptation_note command should be used. -/
  | adaptationNote
  /-- A line ends with windows line endings (\r\n) instead of unix ones (\n). -/
  | windowsLineEnding
  /-- A line contains trailing whitespace. -/
  | trailingWhitespace

deriving BEq

inductive ErrorFormat
  /-- Produce style error output aimed at humans: no error code, clickable file name -/
  | humanReadable : ErrorFormat
  /-- Produce an entry in the style-exceptions file: mention the error code, slightly uglier
  than humand-readable output -/
  | exceptionsFile : ErrorFormat
  /-- Produce output suitable for Github error annotations: in particular,
  duplicate the file path, line number and error code -/
  | github : ErrorFormat
  deriving BEq

def StyleError.errorMessage (err : StyleError) : String := match err with
  | StyleError.adaptationNote =>
    "Found the string \"Adaptation note:\", please use the #adaptation_note command instead"
  | windowsLineEnding => "This line ends with a windows line ending (\r\n): please use Unix line\
    endings (\n) instead"
  | trailingWhitespace => "This line ends with some whitespace: please remove this"

def StyleError.errorCode (err : StyleError) : String := match err with
  | StyleError.adaptationNote => "ERR_ADN"
  | StyleError.windowsLineEnding => "ERR_WIN"
  | StyleError.trailingWhitespace => "ERR_TWS"

structure ErrorContext where
  /-- The underlying `StyleError`-/
  error : StyleError
  /-- The line number of the error (1-based) -/
  lineNumber : ℕ
  /-- The path to the file which was linted -/
  path : FilePath

inductive ComparisonResult
  /-- The contexts describe different errors: two separate style exceptions are required
  to cover both. -/
  | Different
  /-- The existing exception also covers the new error:
  we keep the existing exception. -/
  | Comparable
  deriving BEq

def compare (existing new : ErrorContext) : ComparisonResult :=
  -- Two comparable error contexts must have the same path.
  -- To avoid issues with different path separators across different operating systems,
  -- we compare the set of path components instead.
  if existing.path.components != new.path.components then ComparisonResult.Different
  -- We entirely ignore their line numbers: not sure if this is best.

  -- NB: keep the following in sync with `parse?_errorContext` below.
  -- Generally, comparable errors must have equal `StyleError`s.
  else
    if existing.error == new.error then ComparisonResult.Comparable else ComparisonResult.Different

def ErrorContext.find?_comparable (e : ErrorContext) (exceptions : Array ErrorContext) :
    Option ErrorContext :=
  (exceptions).find? (fun new ↦ compare e new == ComparisonResult.Comparable)

def outputMessage (errctx : ErrorContext) (style : ErrorFormat) : String :=
  let errorMessage := errctx.error.errorMessage
  match style with
  | ErrorFormat.github =>
   -- We are outputting for github: duplicate file path, line number and error code,
    -- so that they are also visible in the plain text output.
    let path := errctx.path
    let nr := errctx.lineNumber
    let code := errctx.error.errorCode
    s!"::ERR file={path},line={nr},code={code}::{path}:{nr} {code}: {errorMessage}"
  | ErrorFormat.exceptionsFile =>
    -- Produce an entry in the exceptions file: with error code and "line" in front of the number.
    s!"{errctx.path} : line {errctx.lineNumber} : {errctx.error.errorCode} : {errorMessage}"
  | ErrorFormat.humanReadable =>
    -- Print for humans: clickable file name and omit the error code
    s!"error: {errctx.path}:{errctx.lineNumber}: {errorMessage}"

def parse?_errorContext (line : String) : Option ErrorContext := Id.run do
  let parts := line.split (· == ' ')
  match parts with
    | filename :: ":" :: "line" :: lineNumber :: ":" :: errorCode :: ":" :: _errorMessage =>
      -- Turn the filename into a path. In general, this is ambiguous if we don't know if we're
      -- dealing with e.g. Windows or POSIX paths. In our setting, this is fine, since no path
      -- component contains any path separator.
      let path := mkFilePath (filename.split (FilePath.pathSeparators.contains ·))
      -- Parse the error kind from the error code, ugh.
      -- NB: keep this in sync with `StyleError.errorCode` above!
      let err : Option StyleError := match errorCode with
        -- Use default values for parameters which are ignored for comparing style exceptions.
        -- NB: keep this in sync with `compare` above!
        | "ERR_ADN" => some (StyleError.adaptationNote)
        | "ERR_TWS" => some (StyleError.trailingWhitespace)
        | "ERR_WIN" => some (StyleError.windowsLineEnding)
        | _ => none
      match String.toNat? lineNumber with
      | some n => err.map fun e ↦ (ErrorContext.mk e n path)
      | _ => none
    -- It would be nice to print an error on any line which doesn't match the above format,
    -- but is awkward to do so (this `def` is not in any IO monad). Hopefully, this is not necessary
    -- anyway as the style exceptions file is mostly automatically generated.
    | _ => none

def parseStyleExceptions (lines : Array String) : Array ErrorContext := Id.run do
  -- We treat all lines starting with "--" as a comment and ignore them.
  Array.filterMap (parse?_errorContext ·) (lines.filter (fun line ↦ !line.startsWith "--"))

def formatErrors (errors : Array ErrorContext) (style : ErrorFormat) : IO Unit := do
  for e in errors do
    IO.println (outputMessage e style)

abbrev TextbasedLinter := Array String → Array (StyleError × ℕ) × (Option (Array String))

/-! Definitions of the actual text-based linters. -/

section

def adaptationNoteLinter : TextbasedLinter := fun lines ↦ Id.run do
  let mut errors := Array.mkEmpty 0
  for (line, idx) in lines.zipWithIndex do
    -- We make this shorter to catch "Adaptation note", "adaptation note" and a missing colon.
    if line.containsSubstr "daptation note" then
      errors := errors.push (StyleError.adaptationNote, idx + 1)
  return (errors, none)

def trailingWhitespaceLinter : TextbasedLinter := fun lines ↦ Id.run do
  let mut errors := Array.mkEmpty 0
  let mut fixedLines := lines
  for (line, idx) in lines.zipWithIndex do
    if line.back == ' ' then
      errors := errors.push (StyleError.trailingWhitespace, idx + 1)
      fixedLines := fixedLines.set! idx line.trimRight
  return (errors, if errors.size > 0 then some fixedLines else none)

def isImportsOnlyFile (lines : Array String) : Bool :=
  -- The Python version also excluded multi-line comments: for all files generated by `mk_all`,
  -- this is in fact not necessary. (It is needed for `Tactic/Linter.lean`, though.)
  lines.all (fun line ↦ line.startsWith "import " || line == "" || line.startsWith "-- ")

end

def allLinters : Array TextbasedLinter := #[
    adaptationNoteLinter, trailingWhitespaceLinter
  ]

def lintFile (path : FilePath) (exceptions : Array ErrorContext) :
    IO (Array ErrorContext × Option (Array String)) := do
  let mut errors := #[]
  -- Whether any changes were made by auto-fixes.
  let mut changes_made := false
  -- Check for windows line endings first: as `FS.lines` treats Unix and Windows lines the same,
  -- we need to analyse the actual file contents.
  let contents ← IO.FS.readFile path
  let replaced := contents.crlfToLf
  if replaced != contents then
    changes_made := true
    errors := errors.push (ErrorContext.mk StyleError.windowsLineEnding 1 path)
  let lines := (replaced.splitOn "\n").toArray

  -- We don't need to run any further checks on imports-only files.
  if isImportsOnlyFile lines then
    return (errors, if changes_made then some lines else none)

  -- All further style errors raised in this file.
  let mut allOutput := #[]
  -- A working copy of the lines in this file, modified by applying the auto-fixes.
  let mut changed := lines

  for lint in allLinters do
    let (err, changes) := lint changed
    allOutput := allOutput.append (Array.map (fun (e, n) ↦ #[(ErrorContext.mk e n path)]) err)
    if let some c := changes then
      changed := c
      changes_made := true
  -- This list is not sorted: for github, this is fine.
  errors := errors.append
    (allOutput.flatten.filter (fun e ↦ (e.find?_comparable exceptions).isNone))
  return (errors, if changes_made then some changed else none)

def lintModules (moduleNames : Array Lean.Name) (style : ErrorFormat) (fix : Bool) : IO UInt32 := do
  -- Read the `nolints` file, with manual exceptions for the linter.
  let nolints ← IO.FS.lines ("scripts" / "nolints-style.txt")
  let styleExceptions := parseStyleExceptions nolints

  let mut numberErrorFiles : UInt32 := 0
  let mut allUnexpectedErrors := #[]
  for module in moduleNames do
    -- Convert the module name to a file name, then lint that file.
    let path := mkFilePath (module.components.map toString)|>.addExtension "lean"

    let (errors, changed) := ← lintFile path styleExceptions
    if let some c := changed then
      if fix then
        let _ := ← IO.FS.writeFile path ("\n".intercalate c.toList)
    if errors.size > 0 then
      allUnexpectedErrors := allUnexpectedErrors.append errors
      numberErrorFiles := numberErrorFiles + 1

  -- Run the remaining python linters. It is easier to just run on all files.
  -- If this poses an issue, I can either filter the output
  -- or wait until lint-style.py is fully rewritten in Lean.
  let args := if fix then #["--fix"] else #[]
  let output ← IO.Process.output { cmd := "./scripts/print-style-errors.sh", args := args }
  if output.exitCode != 0 then
    numberErrorFiles := numberErrorFiles + 1
    IO.eprintln s!"error: `print-style-error.sh` exited with code {output.exitCode}"
    IO.eprint output.stderr
  else if output.stdout != "" then
    numberErrorFiles := numberErrorFiles + 1
    IO.eprint output.stdout
  formatErrors allUnexpectedErrors style
  if allUnexpectedErrors.size > 0 then
    IO.eprintln s!"error: found {allUnexpectedErrors.size} new style error(s)"
  return numberErrorFiles

end Mathlib.Linter.TextBased
