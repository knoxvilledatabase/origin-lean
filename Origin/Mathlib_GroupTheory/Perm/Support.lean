/-
Extracted from GroupTheory/Perm/Support.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# support of a permutation

## Main definitions

In the following, `f g : Equiv.Perm α`.

* `Equiv.Perm.Disjoint`: two permutations `f` and `g` are `Disjoint` if every element is fixed
  either by `f`, or by `g`.
  Equivalently, `f` and `g` are `Disjoint` iff their `support` are disjoint.
* `Equiv.Perm.IsSwap`: `f = swap x y` for `x ≠ y`.
* `Equiv.Perm.support`: the elements `x : α` that are not fixed by `f`.

Assume `α` is a Fintype:
* `Equiv.Perm.fixed_point_card_lt_of_ne_one f` says that `f` has
  strictly less than `Fintype.card α - 1` fixed points, unless `f = 1`.
  (Equivalently, `f.support` has at least 2 elements.)

-/

open Equiv Finset Function

namespace Equiv.Perm

variable {α : Type*}

section Disjoint

def Disjoint (f g : Perm α) :=
  ∀ x, f x = x ∨ g x = x

variable {f g h : Perm α}
