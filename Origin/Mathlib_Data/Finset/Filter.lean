/-
Extracted from Data/Finset/Filter.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Filtering a finite set

## Main declarations

* `Finset.filter`: Given a decidable predicate `p : α → Prop`, `s.filter p` is
  the finset consisting of those elements in `s` satisfying the predicate `p`.

## Tags

finite sets, finset

-/

assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

/-! ### filter -/

section Filter

variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩

end Finset.Filter

namespace Mathlib.Meta

open Lean Elab Term Meta Batteries.ExtendedBinder

meta def knownToBeFinsetNotSet (expectedType? : Option Expr) : TermElabM Bool :=
  -- As we want to reason about the expected type, we would like to wait for it to be available.
  -- However this means that if we fall back on `elabSetBuilder` we will have postponed.
  -- This is undesirable as we want set builder notation to quickly elaborate to a `Set` when no
  -- expected type is available.
  -- tryPostponeIfNoneOrMVar expectedType?
  match expectedType? with
  | some expectedType =>
    match_expr expectedType with
    -- If the expected type is known to be `Finset ?α`, return `true`.
    | Finset _ => pure true
    -- If the expected type is known to be `Set ?α`, give up.
    | Set _ => throwUnsupportedSyntax
    -- If the expected type is known to not be `Finset ?α` or `Set ?α`, return `false`.
    | _ => pure false
  -- If the expected type is not known, return `false`.
  | none => pure false
