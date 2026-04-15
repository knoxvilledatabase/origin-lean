/-
Extracted from GroupTheory/Perm/List.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Permutations from a list

A list `l : List α` can be interpreted as an `Equiv.Perm α` where each element in the list
is permuted to the next one, defined as `formPerm`. When we have that `Nodup l`,
we prove that `Equiv.Perm.support (formPerm l) = l.toFinset`, and that
`formPerm l` is rotationally invariant, in `formPerm_rotate`.

When there are duplicate elements in `l`, how and in what arrangement with respect to the other
elements they appear in the list determines the formed permutation.
This is because `List.formPerm` is implemented as a product of `Equiv.swap`s.
That means that presence of a sublist of two adjacent duplicates like `[..., x, x, ...]`
will produce the same permutation as if the adjacent duplicates were not present.

The `List.formPerm` definition is meant to primarily be used with `Nodup l`, so that
the resulting permutation is cyclic (if `l` has at least two elements).
The presence of duplicates in a particular placement can lead `List.formPerm` to produce a
nontrivial permutation that is noncyclic.
-/

namespace List

variable {α β : Type*}

section FormPerm

variable [DecidableEq α] (l : List α)

open Equiv Equiv.Perm

def formPerm : Equiv.Perm α :=
  (zipWith Equiv.swap l l.tail).prod
