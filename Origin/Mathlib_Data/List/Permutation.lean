/-
Extracted from Data/List/Permutation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Permutations of a list

In this file we prove properties about `List.Permutations`, a list of all permutations of a list. It
is defined in `Data.List.Defs`.

## Order of the permutations

Designed for performance, the order in which the permutations appear in `List.Permutations` is
rather intricate and not very amenable to induction. That's why we also provide `List.Permutations'`
as a less efficient but more straightforward way of listing permutations.

### `List.Permutations`

TODO. In the meantime, you can try decrypting the docstrings.

### `List.Permutations'`

The list of partitions is built by recursion. The permutations of `[]` are `[[]]`. Then, the
permutations of `a :: l` are obtained by taking all permutations of `l` in order and adding `a` in
all positions. Hence, to build `[0, 1, 2, 3].permutations'`, it does
* `[[]]`
* `[[3]]`
* `[[2, 3], [3, 2]]]`
* `[[1, 2, 3], [2, 1, 3], [2, 3, 1], [1, 3, 2], [3, 1, 2], [3, 2, 1]]`
* `[[0, 1, 2, 3], [1, 0, 2, 3], [1, 2, 0, 3], [1, 2, 3, 0],`
   `[0, 2, 1, 3], [2, 0, 1, 3], [2, 1, 0, 3], [2, 1, 3, 0],`
   `[0, 2, 3, 1], [2, 0, 3, 1], [2, 3, 0, 1], [2, 3, 1, 0],`
   `[0, 1, 3, 2], [1, 0, 3, 2], [1, 3, 0, 2], [1, 3, 2, 0],`
   `[0, 3, 1, 2], [3, 0, 1, 2], [3, 1, 0, 2], [3, 1, 2, 0],`
   `[0, 3, 2, 1], [3, 0, 2, 1], [3, 2, 0, 1], [3, 2, 1, 0]]`
-/

assert_not_exists Monoid

open Nat Function

variable {α β : Type*}

namespace List

theorem permutationsAux2_fst (t : α) (ts : List α) (r : List β) :
    ∀ (ys : List α) (f : List α → β), (permutationsAux2 t ts r ys f).1 = ys ++ ts
  | [], _ => rfl
  | y :: ys, f => by simp [permutationsAux2, permutationsAux2_fst t _ _ ys]
