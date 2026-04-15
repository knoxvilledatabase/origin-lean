/-
Extracted from Order/SupClosed.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sets closed under join/meet

This file defines predicates for sets closed under `⊔` and shows that each set in a join-semilattice
generates a join-closed set and that a semilattice where every directed set has a least upper bound
is automatically complete. All dually for `⊓`.

## Main declarations

* `SupClosed`: Predicate for a set to be closed under join (`a ∈ s` and `b ∈ s` imply `a ⊔ b ∈ s`).
* `InfClosed`: Predicate for a set to be closed under meet (`a ∈ s` and `b ∈ s` imply `a ⊓ b ∈ s`).
* `IsSublattice`: Predicate for a set to be closed under meet and join.
* `supClosure`: Sup-closure. Smallest sup-closed set containing a given set.
* `infClosure`: Inf-closure. Smallest inf-closed set containing a given set.
* `latticeClosure`: Smallest sublattice containing a given set.
* `SemilatticeSup.toCompleteSemilatticeSup`: A join-semilattice where every sup-closed set has a
  least upper bound is automatically complete.
* `SemilatticeInf.toCompleteSemilatticeInf`: A meet-semilattice where every inf-closed set has a
  greatest lower bound is automatically complete.
-/

variable {ι : Sort*} {F α β : Type*}

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β]

section Set

variable {ι : Sort*} {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}

open Set

def SupClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊔ b ∈ s
