/-
Extracted from Util/Delaborators.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.PrettyPrinter.Delaborator.Builtins

noncomputable section

/-! # Pi type notation

Provides the `Π x : α, β x` notation as an alternative to Lean 4's built-in
`(x : α) → β x` notation. To get all non-`∀` pi types to pretty print this way
then do `open scoped PiNotation`.

The notation also accepts extended binders, like `Π x ∈ s, β x` for `Π x, x ∈ s → β x`.
-/

namespace PiNotation

open Lean.Parser Term

open Lean.PrettyPrinter.Delaborator

@[term_parser]
def piNotation := leading_parser:leadPrec
  unicodeSymbol "Π" "PiType" >>
  many1 (ppSpace >> (binderIdent <|> bracketedBinder)) >>
  optType >> ", " >> termParser

syntax "Π " binderIdent binderPred ", " term : term

macro_rules
  | `(Π $x:ident $pred:binderPred, $p) => `(Π $x:ident, satisfies_binder_pred% $x $pred → $p)
  | `(Π _ $pred:binderPred, $p) => `(Π x, satisfies_binder_pred% x $pred → $p)

@[macro PiNotation.piNotation] def replacePiNotation : Lean.Macro
  | .node info _ args => return .node info ``Lean.Parser.Term.forall args
  | _ => Lean.Macro.throwUnsupported

@[delab forallE]
def delabPi : Delab := whenPPOption Lean.getPPNotation do
  let stx ← delabForall
  match stx with
  | `(∀ ($i:ident : $_), $j:ident ∈ $s → $body) =>
    if i == j then `(∀ $i:ident ∈ $s, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident > $z → $body) =>
    if x == y then `(∀ $x:ident > $z, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident < $z → $body) =>
    if x == y then `(∀ $x:ident < $z, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident ≥ $z → $body) =>
    if x == y then `(∀ $x:ident ≥ $z, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident ≤ $z → $body) =>
    if x == y then `(∀ $x:ident ≤ $z, $body) else pure stx
  | `(Π ($i:ident : $_), $j:ident ∈ $s → $body) =>
    if i == j then `(Π $i:ident ∈ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ∉ $s → $body) =>
    if i == j then `(∀ $i:ident ∉ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊆ $s → $body) =>
    if i == j then `(∀ $i:ident ⊆ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊂ $s → $body) =>
    if i == j then `(∀ $i:ident ⊂ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊇ $s → $body) =>
    if i == j then `(∀ $i:ident ⊇ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊃ $s → $body) =>
    if i == j then `(∀ $i:ident ⊃ $s, $body) else pure stx
  | _ => pure stx

@[scoped delab forallE]
def delabPi' : Delab := whenPPOption Lean.getPPNotation do
  let stx ← delabPi
  -- Replacements
  let stx : Term ←
    match stx with
    | `($group:bracketedBinder → $body) => `(Π $group:bracketedBinder, $body)
    | _ => pure stx
  -- Merging
  match stx with
  | `(Π $group, Π $groups*, $body) => `(Π $group $groups*, $body)
  | _ => pure stx

end PiNotation

section existential

open Lean Parser Term PrettyPrinter Delaborator

@[delab app.Exists]
def exists_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(∃ (_ : $dom), $body)
      else if prop || ppTypes then
        `(∃ ($x:ident : $dom), $body)
      else
        `(∃ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(∃ $i:ident, $j:ident ∈ $s ∧ $body)
    | `(∃ ($i:ident : $_), $j:ident ∈ $s ∧ $body) =>
      if i == j then `(∃ $i:ident ∈ $s, $body) else pure stx
    | `(∃ $x:ident, $y:ident > $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident > $z ∧ $body) =>
      if x == y then `(∃ $x:ident > $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident < $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident < $z ∧ $body) =>
      if x == y then `(∃ $x:ident < $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ≥ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ≥ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ≥ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ≤ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ≤ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ≤ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ∉ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ∉ $z ∧ $body) => do
      if x == y then `(∃ $x:ident ∉ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊆ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊆ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊆ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊂ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊂ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊂ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊇ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊇ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊇ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊃ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊃ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊃ $z, $body) else pure stx
    | _ => pure stx
  match stx with
  | `(∃ $group:bracketedExplicitBinders, ∃ $[$groups:bracketedExplicitBinders]*, $body) =>
    `(∃ $group $groups*, $body)
  | `(∃ $b:binderIdent, ∃ $[$bs:binderIdent]*, $body) => `(∃ $b:binderIdent $[$bs]*, $body)
  | _ => pure stx

end existential

open Lean Lean.PrettyPrinter.Delaborator

@[delab app.Not] def delab_not_in := whenPPOption Lean.getPPNotation do
  let #[f] := (← SubExpr.getExpr).getAppArgs | failure
  guard <| f.isAppOfArity ``Membership.mem 5
  let stx₁ ← SubExpr.withAppArg <| SubExpr.withNaryArg 3 delab
  let stx₂ ← SubExpr.withAppArg <| SubExpr.withNaryArg 4 delab
  return ← `($stx₂ ∉ $stx₁)
