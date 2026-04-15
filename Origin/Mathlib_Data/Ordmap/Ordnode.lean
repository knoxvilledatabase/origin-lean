/-
Extracted from Data/Ordmap/Ordnode.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Ordered sets

This file defines a data structure for ordered sets, supporting a
variety of useful operations including insertion and deletion,
logarithmic time lookup, set operations, folds,
and conversion from lists.

The `Ordnode α` operations all assume that `α` has the structure of
a total preorder, meaning a `≤` operation that is

* Transitive: `x ≤ y → y ≤ z → x ≤ z`
* Reflexive: `x ≤ x`
* Total: `x ≤ y ∨ y ≤ x`

For example, in order to use this data structure as a map type, one
can store pairs `(k, v)` where `(k, v) ≤ (k', v')` is defined to mean
`k ≤ k'` (assuming that the key values are linearly ordered).

Two values `x,y` are equivalent if `x ≤ y` and `y ≤ x`. An `Ordnode α`
maintains the invariant that it never stores two equivalent nodes;
the insertion operation comes with two variants depending on whether
you want to keep the old value or the new value in case you insert a value
that is equivalent to one in the set.

The operations in this file are not verified, in the sense that they provide
"raw operations" that work for programming purposes but the invariants
are not explicitly in the structure. See `Ordset` for a verified version
of this data structure.

## Main definitions

* `Ordnode α`: A set of values of type `α`

## Implementation notes

Based on weight balanced trees:

* Stephen Adams, "Efficient sets: a balancing act",
  Journal of Functional Programming 3(4):553-562, October 1993,
  <http://www.swiss.ai.mit.edu/~adams/BB/>.
* J. Nievergelt and E.M. Reingold,
  "Binary search trees of bounded balance",
  SIAM journal of computing 2(1), March 1973.

Ported from Haskell's `Data.Set`.

## Tags

ordered map, ordered set, data structure

-/

universe u

inductive Ordnode (α : Type u) : Type u
  | nil : Ordnode α
  | node (size : ℕ) (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α

compile_inductive% Ordnode

namespace Ordnode

variable {α : Type*}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
