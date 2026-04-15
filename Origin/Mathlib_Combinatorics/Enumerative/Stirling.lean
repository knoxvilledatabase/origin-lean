/-
Extracted from Combinatorics/Enumerative/Stirling.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Stirling Numbers

This file defines Stirling numbers of the first and second kinds, proves their fundamental
recurrence relations, and establishes some of their key properties and identities.

## The Stirling numbers of the first kind

The unsigned Stirling numbers of the first kind, represent the number of ways
to partition `n` distinct elements into `k` non-empty cycles.

## The Stirling numbers of the second kind

The Stirling numbers of the second kind, represent the number of ways to partition
`n` distinct elements into `k` non-empty subsets.

## Main definitions

* `Nat.stirlingFirst`: the number of ways to partition `n` distinct elements into `k` non-empty
  cycles, defined by the recursive relationship it satisfies.
* `Nat.stirlingSecond`: the number of ways to partition `n` distinct elements into `k` non-empty
  subsets, defined by the recursive relationship it satisfies.

## References

* [Knuth, *The Art of Computer Programming*, Volume 1, §1.2.6][knuth1997]
-/

open Nat

namespace Nat

def stirlingFirst : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * stirlingFirst n (k + 1) + stirlingFirst n k
