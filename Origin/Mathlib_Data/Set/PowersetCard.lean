/-
Extracted from Data/Set/PowersetCard.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Combinations

Combinations in a type are finite subsets of given cardinality.

* `Set.powersetCard α n` is the set of all `Finset α` with cardinality `n`.
  The name is chosen in relation with `Finset.powersetCard` which corresponds to
  the analogous structure for subsets of given cardinality of a given `Finset`, as a `Finset`.

* `Set.powersetCard.card` proves that the `Nat.card`-cardinality
  of this set is equal to `(Nat.card α).choose n`.

-/

variable (α : Type*)

def Set.powersetCard (n : ℕ) := {s : Finset α | s.card = n}

variable {α} {n : ℕ}

namespace Set.powersetCard

open Finset Set Function
