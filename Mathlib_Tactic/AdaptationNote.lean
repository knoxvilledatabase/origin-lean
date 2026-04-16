/-
Extracted from Tactic/AdaptationNote.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Meta.Tactic.TryThis

noncomputable section

/-!
# Adaptation notes

This file defines a `#adaptation_note` command.
Adaptation notes are comments that are used to indicate that a piece of code
has been changed to accommodate a change in Lean core.
They typically require further action/maintenance to be taken in the future.
-/

open Lean

initialize registerTraceClass `adaptationNote

def reportAdaptationNote (f : Syntax → Meta.Tactic.TryThis.Suggestion) : MetaM Unit := do
  let stx ← getRef
  if let some doc := stx[1].getOptional? then
    trace[adaptationNote] (Lean.TSyntax.getDocString ⟨doc⟩)
  else
    logError "Adaptation notes must be followed by a /-- comment -/"
    let trailing := if let .original (trailing := s) .. := stx[0].getTailInfo then s else default
    let doc : Syntax :=
      Syntax.node2 .none ``Parser.Command.docComment (mkAtom "/--") (mkAtom "comment -/")
    -- Optional: copy the original whitespace after the `#adaptation_note` token
    -- to after the docstring comment
    let doc := doc.updateTrailing trailing
    let stx' := (← getRef)
    let stx' := stx'.setArg 0 stx'[0].unsetTrailing
    let stx' := stx'.setArg 1 (mkNullNode #[doc])
    Meta.Tactic.TryThis.addSuggestion (← getRef) (f stx') (origSpan? := ← getRef)

elab (name := adaptationNoteCmd) "#adaptation_note " (docComment)? : command => do
  Elab.Command.liftTermElabM <| reportAdaptationNote (fun s => (⟨s⟩ : TSyntax `tactic))

elab "#adaptation_note " (docComment)? : tactic =>
  reportAdaptationNote (fun s => (⟨s⟩ : TSyntax `tactic))

syntax (name := adaptationNoteTermStx) "#adaptation_note " (docComment)? term : term

@[term_elab adaptationNoteTermStx]
def adaptationNoteTermElab : Elab.Term.TermElab
  | `(#adaptation_note $[$_]? $t) => fun expectedType? => do
    reportAdaptationNote (fun s => (⟨s⟩ : Term))
    Elab.Term.elabTerm t expectedType?
  | _ => fun _ => Elab.throwUnsupportedSyntax

example : True := by
  #adaptation_note /-- This is a test -/
  trivial

example : True :=
  #adaptation_note /-- This is a test -/
  trivial
