/-
Extracted from Data/Setoid/Partition.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivalence relations: partitions

This file comprises properties of equivalence relations viewed as partitions.
There are two implementations of partitions here:
* A collection `c : Set (Set α)` of sets is a partition of `α` if `∅ ∉ c` and each element `a : α`
  belongs to a unique set `b ∈ c`. This is expressed as `IsPartition c`
* An indexed partition is a map `s : ι → Set α` whose image is a partition. This is
  expressed as `IndexedPartition s`.

Of course both implementations are related to `Quotient` and `Setoid`.

`Setoid.isPartition.partition` and `Finpartition.isPartition_parts` furnish
a link between `Setoid.IsPartition` and `Finpartition`.

## TODO

Could the design of `Finpartition` inform the one of `Setoid.IsPartition`? Maybe bundling it and
changing it from `Set (Set α)` to `Set α` where `[Lattice α] [OrderBot α]` would make it more
usable.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence class
-/

namespace Setoid

variable {α : Type*}

theorem eq_of_mem_eqv_class {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {x b b'}
    (hc : b ∈ c) (hb : x ∈ b) (hc' : b' ∈ c) (hb' : x ∈ b') : b = b' :=
  (H x).unique ⟨hc, hb⟩ ⟨hc', hb'⟩
