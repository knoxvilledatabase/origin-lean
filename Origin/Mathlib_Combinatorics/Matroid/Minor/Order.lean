/-
Extracted from Combinatorics/Matroid/Minor/Order.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matroid Minors

A matroid `N = M ／ C ＼ D` obtained from a matroid `M` by a contraction then a delete,
(or equivalently, by any number of contractions/deletions in any order) is a *minor* of `M`.
This gives a partial order on `Matroid α` that is ubiquitous in matroid theory,
and interacts nicely with duality and linear representations.

Although we provide a `PartialOrder` instance on `Matroid α` corresponding to the minor order,
we do not use the `M ≤ N` / `N < M` notation directly,
instead writing `N ≤m M` and `N <m M` for more convenient dot notation.

## Main Declarations

* `Matroid.IsMinor N M`, written `N ≤m M`, means that `N = M ／ C ＼ D` for some
  subset `C` and `D` of `M.E`.
* `Matroid.IsStrictMinor N M`, written `N <m M`, means that `N = M ／ C ＼ D`
  for some subsets `C` and `D` of `M.E` that are not both nonempty.
* `Matroid.IsMinor.exists_eq_contract_delete_disjoint` : we can choose `C` and `D` disjoint.

-/

namespace Matroid

open Set

section Minor

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I C D : Set α}

/-! ### Minors -/

def IsMinor (N M : Matroid α) : Prop := ∃ C D, N = M ／ C ＼ D

infixl:50 " ≤m " => Matroid.IsMinor
