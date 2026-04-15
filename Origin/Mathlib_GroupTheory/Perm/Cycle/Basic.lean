/-
Extracted from GroupTheory/Perm/Cycle/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cycles of a permutation

This file starts the theory of cycles in permutations.

## Main definitions

In the following, `f : Equiv.Perm β`.

* `Equiv.Perm.SameCycle`: `f.SameCycle x y` when `x` and `y` are in the same cycle of `f`.
* `Equiv.Perm.IsCycle`: `f` is a cycle if any two nonfixed points of `f` are related by repeated
  applications of `f`, and `f` is not the identity.
* `Equiv.Perm.IsCycleOn`: `f` is a cycle on a set `s` when any two points of `s` are related by
  repeated applications of `f`.

## Notes

`Equiv.Perm.IsCycle` and `Equiv.Perm.IsCycleOn` are different in three ways:
* `IsCycle` is about the entire type while `IsCycleOn` is restricted to a set.
* `IsCycle` forbids the identity while `IsCycleOn` allows it (if `s` is a subsingleton).
* `IsCycleOn` forbids fixed points on `s` (if `s` is nontrivial), while `IsCycle` allows them.
-/

open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

/-! ### `SameCycle` -/

section SameCycle

variable {f g : Perm α} {p : α → Prop} {x y z : α}

def SameCycle (f : Perm α) (x y : α) : Prop :=
  ∃ i : ℤ, (f ^ i) x = y
