/-
Extracted from Combinatorics/Enumerative/DyckWord.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dyck words

A Dyck word is a sequence consisting of an equal number `n` of symbols of two types such that
for all prefixes one symbol occurs at least as many times as the other.
If the symbols are `(` and `)` the latter restriction is equivalent to balanced brackets;
if they are `U = (1, 1)` and `D = (1, -1)` the sequence is a lattice path from `(0, 0)` to `(0, 2n)`
and the restriction requires the path to never go below the x-axis.

This file defines Dyck words and constructs their bijection with rooted binary trees,
one consequence being that the number of Dyck words with length `2 * n` is `catalan n`.

## Main definitions

* `DyckWord`: a list of `U`s and `D`s with as many `U`s as `D`s and with every prefix having
  at least as many `U`s as `D`s.
* `DyckWord.semilength`: semilength (half the length) of a Dyck word.
* `DyckWord.firstReturn`: for a nonempty word, the index of the `D` matching the initial `U`.

## Main results

* `DyckWord.equivTree`: equivalence between Dyck words and rooted binary trees.
  See the docstrings of `DyckWord.toTree` and `DyckWord.ofTree` for details.
* `DyckWord.equivTreesOfNumNodesEq`: equivalence between Dyck words of length `2 * n` and
  rooted binary trees with `n` internal nodes.
* `DyckWord.card_dyckWord_semilength_eq_catalan`:
  there are `catalan n` Dyck words of length `2 * n` or semilength `n`.

## Implementation notes

While any two-valued type could have been used for `DyckStep`, a new enumerated type is used here
to emphasise that the definition of a Dyck word does not depend on that underlying type.
-/

open List

inductive DyckStep
  | U : DyckStep
  | D : DyckStep
  deriving Inhabited, DecidableEq

lemma DyckStep.dichotomy (s : DyckStep) : s = U ∨ s = D := by cases s <;> tauto

open DyckStep
