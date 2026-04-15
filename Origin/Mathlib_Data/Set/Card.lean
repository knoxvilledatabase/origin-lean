/-
Extracted from Data/Set/Card.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Noncomputable Set Cardinality

We define the cardinality of set `s` as a term `Set.encard s : ℕ∞` and a term `Set.ncard s : ℕ`.
The latter takes the junk value of zero if `s` is infinite. Both functions are noncomputable, and
are defined in terms of `ENat.card` (which takes a type as its argument); this file can be seen
as an API for the same function in the special case where the type is a coercion of a `Set`,
allowing for smoother interactions with the `Set` API.

`Set.encard` never takes junk values, so is more mathematically natural than `Set.ncard`, even
though it takes values in a less convenient type. It is probably the right choice in settings where
one is concerned with the cardinalities of sets that may or may not be infinite.

`Set.ncard` has a nicer codomain, but when using it, `Set.Finite` hypotheses are normally needed to
make sure its values are meaningful.  More generally, `Set.ncard` is intended to be used over the
obvious alternative `Finset.card` when finiteness is 'propositional' rather than 'structural'.
When working with sets that are finite by virtue of their definition, then `Finset.card` probably
makes more sense. One setting where `Set.ncard` works nicely is in a type `α` with `[Finite α]`,
where every set is automatically finite. In this setting, we use default arguments and a simple
tactic so that finiteness goals are discharged automatically in `Set.ncard` theorems.

## Main Definitions

* `Set.encard s` is the cardinality of the set `s` as an extended natural number, with value `⊤` if
    `s` is infinite.
* `Set.ncard s` is the cardinality of the set `s` as a natural number, provided `s` is Finite.
  If `s` is Infinite, then `Set.ncard s = 0`.
* `toFinite_tac` is a tactic that tries to synthesize a `Set.Finite s` argument with
  `Set.toFinite`. This will work for `s : Set α` where there is a `Finite α` instance.

## Implementation Notes

The theorems in this file are very similar to those in `Mathlib/Data/Finset/Card.lean`, but with
`Set` operations instead of `Finset`. We first prove all the theorems for `Set.encard`, and then
derive most of the `Set.ncard` results as a consequence. Things are done this way to avoid reliance
on the `Finset` API for theorems about infinite sets, and to allow for a refactor that removes or
modifies `Set.ncard` in the future.

Nearly all the theorems for `Set.ncard` require finiteness of one or more of their arguments. We
provide this assumption with a default argument of the form `(hs : s.Finite := by toFinite_tac)`,
where `toFinite_tac` will find an `s.Finite` term in the cases where `s` is a set in a `Finite`
type.

Often, where there are two set arguments `s` and `t`, the finiteness of one follows from the other
in the context of the theorem, in which case we only include the ones that are needed, and derive
the other inside the proof. A few of the theorems, such as `ncard_union_le` do not require
finiteness arguments; they are true by coincidence due to junk values.
-/

namespace Set

variable {α β : Type*} {s t : Set α}

noncomputable def encard (s : Set α) : ℕ∞ := ENat.card s
