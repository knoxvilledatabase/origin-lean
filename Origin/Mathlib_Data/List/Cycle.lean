/-
Extracted from Data/List/Cycle.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cycles of a list

Lists have an equivalence relation of whether they are rotational permutations of one another.
This relation is defined as `IsRotated`.

Based on this, we define the quotient of lists by the rotation relation, called `Cycle`.

We also define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representable types. For example, the cycle `(2 1 4 3)` will be shown
as `c[2, 1, 4, 3]`. Two equal cycles may be printed differently if their internal representation
is different.

-/

assert_not_exists MonoidWithZero

namespace List

variable {α : Type*} [DecidableEq α]

def nextOr : ∀ (_ : List α) (_ _ : α), α
  | [], _, default => default
  | [_], _, default => default
  -- Handles the not-found and the wraparound case
  | y :: z :: xs, x, default => if x = y then z else nextOr (z :: xs) x default
