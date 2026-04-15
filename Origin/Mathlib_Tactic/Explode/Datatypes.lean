/-
Extracted from Tactic/Explode/Datatypes.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Util.Trace

/-!
# Explode command: datatypes

This file contains datatypes used by the `#explode` command and their associated methods.
-/

open Lean

namespace Mathlib.Explode

initialize registerTraceClass `explode

inductive Status where
  /-- `├` Start intro (top-level) -/
  | sintro : Status
  /-- `Entry.depth` * `│` + `┌` Normal intro -/
  | intro  : Status
  /-- `Entry.depth` * `│` + `├` Continuation intro -/
  | cintro : Status
  /-- `Entry.depth` * `│` -/
  | lam    : Status
  /-- `Entry.depth` * `│` -/
  | reg    : Status
  deriving Inhabited

structure Entry where
  /-- A type of this expression as a `MessageData`. Make sure to use `addMessageContext`. -/
  type     : MessageData
  /-- The row number, starting from `0`. This is set by `Entries.add`. -/
  line     : Option Nat := none
  /-- How many `if`s (aka lambda-abstractions) this row is nested under. -/
  depth    : Nat
  /-- What `Status` this entry has - this only affects how `│`s are displayed. -/
  status   : Status
  /-- What to display in the "theorem applied" column.
  Make sure to use `addMessageContext` if needed. -/
  thm      : MessageData
  /-- Which other lines (aka rows) this row depends on.
  `none` means that the dependency has been filtered out of the table. -/
  deps     : List (Option Nat)
  /-- Whether or not to use this in future deps lists. Generally controlled by the `select` function
  passed to `explodeCore`. Exception: `∀I` may ignore this for introduced hypotheses. -/
  useAsDep : Bool

def Entry.line! (entry : Entry) : Nat := entry.line.get!

structure Entries : Type where
  /-- Allows us to compare `Expr`s fast. -/
  s : ExprMap Entry
  /-- Simple list of `Expr`s. -/
  l : List Entry
  deriving Inhabited

def Entries.find? (es : Entries) (e : Expr) : Option Entry :=
  es.s[e]?

def Entries.size (es : Entries) : Nat :=
  es.s.size

def Entries.add (entries : Entries) (expr : Expr) (entry : Entry) : Entry × Entries :=
  if let some entry' := entries.find? expr then
    (entry', entries)
  else
    let entry := { entry with line := entries.size }
    (entry, ⟨entries.s.insert expr entry, entry :: entries.l⟩)

def Entries.addSynonym (entries : Entries) (expr : Expr) (entry : Entry) : Entries :=
  ⟨entries.s.insert expr entry, entries.l⟩

end Explode

end Mathlib
