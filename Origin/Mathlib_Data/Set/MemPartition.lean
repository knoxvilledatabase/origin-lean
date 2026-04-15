/-
Extracted from Data/Set/MemPartition.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Partitions based on membership of a sequence of sets

Let `f : ℕ → Set α` be a sequence of sets. For `n : ℕ`, we can form the set of points that are in
`f 0 ∪ f 1 ∪ ... ∪ f (n-1)`; then the set of points in `(f 0)ᶜ ∪ f 1 ∪ ... ∪ f (n-1)` and so on for
all 2^n choices of a set or its complement. The at most 2^n sets we obtain form a partition
of `univ : Set α`. We call that partition `memPartition f n` (the membership partition of `f`).
For `n = 0` we set `memPartition f 0 = {univ}`.

The partition `memPartition f (n + 1)` is finer than `memPartition f n`.

## Main definitions

* `memPartition f n`: the membership partition of the first `n` sets in `f`.
* `memPartitionSet`: `memPartitionSet f n x` is the set in the partition `memPartition f n` to
  which `x` belongs.

## Main statements

* `disjoint_memPartition`: the sets in `memPartition f n` are disjoint
* `sUnion_memPartition`: the union of the sets in `memPartition f n` is `univ`
* `finite_memPartition`: `memPartition f n` is finite

-/

open Set

variable {α : Type*}

def memPartition (f : ℕ → Set α) : ℕ → Set (Set α)
  | 0 => {univ}
  | n + 1 => {s | ∃ u ∈ memPartition f n, s = u ∩ f n ∨ s = u \ f n}
