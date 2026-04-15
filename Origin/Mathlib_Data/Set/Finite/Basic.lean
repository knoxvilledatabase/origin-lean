/-
Extracted from Data/Set/Finite/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite sets

This file provides `Fintype` instances for many set constructions. It also proves basic facts about
finite sets and gives ways to manipulate `Set.Finite` expressions.

Note that the instances in this file are selected somewhat arbitrarily on the basis of them not
needing any imports beyond `Data.Fintype.Card` (which is required by `Finite.ofFinset`); they can
certainly be organized better.

## Main definitions

* `Set.Finite.toFinset` to noncomputably produce a `Finset` from a `Set.Finite` proof.
  (See `Set.toFinset` for a computable version.)

## Implementation

A finite set is defined to be a set whose coercion to a type has a `Finite` instance.

There are two components to finiteness constructions. The first is `Fintype` instances for each
construction. This gives a way to actually compute a `Finset` that represents the set, and these
may be accessed using `set.toFinset`. This gets the `Finset` in the correct form, since otherwise
`Finset.univ : Finset s` is a `Finset` for the subtype for `s`. The second component is
"constructors" for `Set.Finite` that give proofs that `Fintype` instances exist classically given
other `Set.Finite` proofs. Unlike the `Fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite sets
-/

assert_not_exists Monoid

open Set Function

open scoped symmDiff

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

theorem finite_def {s : Set α} : s.Finite ↔ Nonempty (Fintype s) :=
  finite_iff_nonempty_fintype s

protected alias ⟨Finite.nonempty_fintype, _⟩ := finite_def

protected theorem Finite.ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : p.Finite :=
  have := Fintype.ofFinset s H; p.toFinite
