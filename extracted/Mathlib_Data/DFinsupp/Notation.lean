/-
Extracted from Data/DFinsupp/Notation.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.Finsupp.Notation

noncomputable section

/-!
# Notation for `DFinsupp`

This file extends the existing `fun₀ | 3 => a | 7 => b` notation to work for `DFinsupp`,
which desugars to `DFinsupp.update` and `DFinsupp.single`,
in the same way that `{a, b}` desugars to `insert` and `singleton`.

Note that this syntax is for `Finsupp` by default, but works for `DFinsupp` if the expected type
is correct.
-/

namespace DFinsupp

open Lean Parser Term

attribute [term_parser] Finsupp.stxSingle₀ Finsupp.stxUpdate₀

@[term_elab Finsupp.stxSingle₀]
def elabSingle₀ : Elab.Term.TermElab
  | `(term| single₀ $i $x) => fun ty? => do
    Elab.Term.tryPostponeIfNoneOrMVar ty?
    let .some ty := ty? | Elab.throwUnsupportedSyntax
    let_expr DFinsupp _ _ _ := ← Meta.withReducible (Meta.whnf ty) | Elab.throwUnsupportedSyntax
    Elab.Term.elabTerm (← `(DFinsupp.single $i $x)) ty?
  | _ => fun _ => Elab.throwUnsupportedSyntax

@[term_elab Finsupp.stxUpdate₀]
def elabUpdate₀ : Elab.Term.TermElab
  | `(term| update₀ $f $i $x) => fun ty? => do
    Elab.Term.tryPostponeIfNoneOrMVar ty?
    let .some ty := ty? | Elab.throwUnsupportedSyntax
    let_expr DFinsupp _ _ _ := ← Meta.withReducible (Meta.whnf ty) | Elab.throwUnsupportedSyntax
    Elab.Term.elabTerm (← `(DFinsupp.update $f $i $x)) ty?
  | _ => fun _ => Elab.throwUnsupportedSyntax

@[app_unexpander DFinsupp.single]
def singleUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $pat $val) => `(fun₀ | $pat => $val)
  | _ => throw ()

@[app_unexpander DFinsupp.update]
def updateUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $pat $val) => match f with
    | `(fun₀ $xs:matchAlt*) => `(fun₀ $xs:matchAlt* | $pat => $val)
    | _ => throw ()
  | _ => throw ()

unsafe instance {α : Type*} {β : α → Type*} [Repr α] [∀ i, Repr (β i)] [∀ i, Zero (β i)] :
    Repr (Π₀ a, β a) where
  reprPrec f p :=
    let vals :=
      ((f.support'.unquot.val.map fun i => (repr i, repr (f i))).filter
        (fun p => toString p.2 != "0")).unquot
    let vals_dedup := vals.foldl (fun xs x => x :: xs.eraseP (toString ·.1 == toString x.1)) []
    if vals.length = 0 then
      "0"
    else
      let ret : Std.Format := f!"fun₀" ++ .nest 2 (
        .group (.join <| vals_dedup.map fun a =>
          .line ++ .group (f!"| {a.1} =>" ++ .line ++ a.2)))
      if p ≥ leadPrec then Format.paren ret else ret

end DFinsupp
