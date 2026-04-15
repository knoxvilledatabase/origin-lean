/-
Extracted from Tactic/Lemma.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Parser.Command

/-!
# Support for `lemma` as a synonym for `theorem`.
-/

open Lean

syntax (name := lemma) (priority := default + 1) declModifiers

  group("lemma " declId ppIndent(declSig) declVal) : command

@[macro «lemma»] def expandLemma : Macro := fun stx =>
  -- Not using a macro match, to be more resilient against changes to `lemma`.
  -- This implementation ensures that any future changes to `theorem` are reflected in `lemma`
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration
