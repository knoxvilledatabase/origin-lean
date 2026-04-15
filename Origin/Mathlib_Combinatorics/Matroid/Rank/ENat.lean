/-
Extracted from Combinatorics/Matroid/Rank/ENat.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `ℕ∞`-valued rank

If the 'cardinality' of `s : Set α` is taken to mean the `ℕ∞`-valued term `Set.encard s`,
then all bases of any `M : Matroid α` have the same cardinality,
and for each `X : Set α` with `X ⊆ M.E`, all `M`-bases for `X` have the same cardinality.
The 'rank' of a matroid is the cardinality of all its bases,
and the 'rank' of a set `X` in a matroid `M` is the cardinality of each `M`-basis of `X`.
This file defines these two concepts as a term `Matroid.eRank M : ℕ∞`
and a function `Matroid.eRk M : Set α → ℕ∞` respectively.

The rank function `Matroid.eRk` satisfies three properties, often known as (R1), (R2), (R3):
* `M.eRk X ≤ Set.encard X`,
* `M.eRk X ≤ M.eRk Y` for all `X ⊆ Y`,
* `M.eRk X + M.eRk Y ≥ M.eRk (X ∪ Y) + M.eRk (X ∩ Y)` for all `X, Y`.

In fact, if `α` is finite, then any function `Set α → ℕ∞` satisfying these properties
is the rank function of a `Matroid α`; in other words, properties (R1) - (R3) give an alternative
definition of finite matroids, and a finite matroid is determined by its rank function.
Because of this, and the convenient quantitative language of these axioms,
the rank function is often the preferred perspective on matroids in the literature.
(The above doesn't work as well for infinite matroids,
which is why mathlib defines matroids using bases/independence. )

## Main Declarations

* `Matroid.eRank M` is the `ℕ∞`-valued cardinality of each base of `M`.
* `Matroid.eRk M X` is the `ℕ∞`-valued cardinality of each `M`-basis of `X`.
* `Matroid.eRk_inter_add_eRk_union_le` : the function `M.eRk` is submodular.
* `Matroid.dual_eRk_add_eRank` : a subtraction-free formula for the dual rank of a set.

## Notes

It is natural to ask if equicardinality of bases holds if 'cardinality' refers to
a term in `Cardinal` instead of `ℕ∞`, but the answer is that it doesn't.
The cardinal-valued rank functions `Matroid.cRank` and `Matroid.cRk` are defined in
`Mathlib/Combinatorics/Matroid/Rank/Cardinal.lean`, but have less desirable properties in general.
See the module docstring of that file for a discussion.

## Implementation Details

It would be equivalent to define `Matroid.eRank (M : Matroid α) := (Matroid.cRank M).toENat`
and similar for `Matroid.eRk`, and some of the API for `cRank`/`cRk` would carry over
in a way that shortens certain proofs in this file (though not substantially).
Although this file transitively imports `Cardinal` via `Set.encard`,
there are plans to refactor the latter to be independent of the former,
which would carry over to the current version of this file.
-/

open Set ENat

namespace Matroid

variable {α : Type*} {M : Matroid α} {I B X Y : Set α} {n : ℕ∞} {e f : α}

section Basic

noncomputable def eRank (M : Matroid α) : ℕ∞ := ⨆ B : {B // M.IsBase B}, B.1.encard

noncomputable def eRk (M : Matroid α) (X : Set α) : ℕ∞ := (M ↾ X).eRank

lemma eRank_def (M : Matroid α) : M.eRank = M.eRk M.E := by
  rw [eRk, restrict_ground_eq_self]
