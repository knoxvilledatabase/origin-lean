/-
Extracted from Combinatorics/Enumerative/Bell.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Bell numbers for multisets

For `n : ℕ`, the `n`th Bell number is the number of partitions of a set of cardinality `n`.
Here, we define a refinement of these numbers, that count, for any `m : Multiset ℕ`,
the number of partitions of a set of cardinality `m.sum` whose parts have cardinalities
given by `m`.

The definition presents it as a natural number.

* `Multiset.bell`: number of partitions of a set whose parts have cardinalities a given multiset

* `Nat.uniformBell m n` : short name for `Multiset.bell (replicate m n)`

* `Multiset.bell_mul_eq` shows that
  `m.bell * (m.map (fun j ↦ j !)).prod * Π j ∈ (m.toFinset.erase 0), (m.count j)! = m.sum !`

* `Nat.uniformBell_mul_eq`  shows that
  `uniformBell m n * n ! ^ m * m ! = (m * n) !`

* `Nat.uniformBell_succ_left` computes `Nat.uniformBell (m + 1) n` from `Nat.uniformBell m n`

* `Nat.bell n`: the `n`th standard Bell number,
  which counts the number of partitions of a set of cardinality `n`

* `Nat.bell_succ n` shows that
  `Nat.bell (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.bell (n - k)`

## TODO

Prove that it actually counts the number of partitions as indicated.
(When `m` contains `0`, the result requires to admit repetitions of the empty set as a part.)

-/

open Multiset Nat

namespace Multiset

def bell (m : Multiset ℕ) : ℕ :=
  Nat.multinomial m.toFinset (fun k ↦ k * m.count k) *
    ∏ k ∈ m.toFinset.erase 0, ∏ j ∈ .range (m.count k), (j * k + k - 1).choose (k - 1)
