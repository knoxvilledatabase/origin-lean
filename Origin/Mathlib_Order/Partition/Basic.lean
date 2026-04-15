/-
Extracted from Order/Partition/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Partitions

A `Partition` of an element `a` in a complete lattice is an independent family of nontrivial
elements whose supremum is `a`.

An important special case is where `s : Set α`, where a `Partition s` corresponds to a partition
of the elements of `s` into a family of nonempty sets.
This is equivalent to a transitive and symmetric binary relation `r : α → α → Prop`
where `s` is the set of all `x` for which `r x x`.

Partitions are ordered by refinement: `P ≤ Q` if every part of `P` is less than or equal to a part
of `Q`.

## Main definitions

* `Partition s`: For `[CompleteLattice α]` and `s : α`, a `Partition s` is an independent
  collection of nontrivial elements whose supremum is `s`.
* `Partition.removeBot`: A constructor for `Partition s` that removes `⊥` from a set of parts.
* `Partition.Rel`: The partial equivalence relation induced by a partition of a set.
* `Partition.IsRepFun`: A predicate characterizing a representative function for a partition.

## Representative functions (`IsRepFun`)

`IsRepFun P f` means that `f` sends each element of the support to a representative in its
`Partition.Rel`-class, agrees on related elements, and is the identity outside the support.

This is useful whenever a construction must pick one distinguished element per part of a partition.
For example, in graph theory one may partition edges into parallel classes or vertices into
connected components; a representative function can specify which edge remains when simplifying
parallel edges, or how supervertices are labeled after contraction. Similar uses arise in matroid
theory and in the definition of minors.

Tempting alternatives are to use `Classical.choice` or fix a global well-order and take minimal
representatives. However, these lead to issues with inconsistencies: independent choices need not
respect relations between different instances (e.g. monotonicity of simplifications with respect
to subgraph order), a global order can clash with structure already carried by the type, and maps
between different types need not intertwine two separate canonical choices. Stating hypotheses with
`IsRepFun` keeps the chosen representatives explicit; existence under suitable conditions can be
proved separately.

## TODO

* Link this to `Finpartition`.

-/

variable {α : Type*} {s t x y z : α} {S : Set α}

open Set

structure Partition [CompleteLattice α] (s : α) where
  /-- The collection of parts -/
  parts : Set α
  /-- The parts are `sSupIndep`. -/
  sSupIndep' : sSupIndep parts
  /-- The bottom element is not a part. -/
  bot_notMem' : ⊥ ∉ parts
  /-- The supremum of all parts is `s`. -/
  sSup_eq' : sSup parts = s

namespace Partition

section Basic

variable [CompleteLattice α] {P Q : Partition s}

-- INSTANCE (free from Core): {s

def Simps.coe {s : α} (P : Partition s) : Set α := P

initialize_simps_projections Partition (parts → coe, as_prefix coe)
