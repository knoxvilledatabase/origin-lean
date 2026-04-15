/-
Extracted from Combinatorics/Enumerative/Partition/GenFun.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Generating functions for partitions

This file defines generating functions related to partitions. Given a character function $f(i, c)$
of a part $i$ and the number of occurrences of the part $c$, the related generating function is
$$
G_f(X) = \sum_{n = 0}^{\infty} \left(\sum_{p \in P_{n}} \prod_{i \in p} f(i, \#i)\right) X^n
= \prod_{i = 1}^{\infty}\left(1 + \sum_{j = 1}^{\infty} f(i, j) X^{ij}\right)
$$
where $P_n$ is all partitions of $n$, $\#i$ is the count of $i$ in the partition $p$.
We give the definition `Nat.Partition.genFun` using the first equation, and prove the second
equation in `Nat.Partition.hasProd_genFun` (with shifted indices).

This generating function can be specialized to
* When $f(i, c) = 1$, this is the generating function for partition function $p(n)$
  (TODO: prove this).
* When $f(i, 1) = 1$ and $f(i, c) = 0$ for $c > 1$, this is the generating function for
  `#(Nat.Partition.distincts n)`. More generally, setting $f(i, c) = 1$ only for $c < m$ gives
  the generating function for `#(Nat.Partition.countRestricted n m)`.
  (See `Nat.Partition.hasProd_powerSeriesMk_card_countRestricted`).
* When $f(i, c) = 1$ for odd $i$ and $f(i, c) = 0$ for even $i$, this is the generating function for
  `#(Nat.Partition.odds n)`. More generally, setting $f(i, c) = 1$ only for $i$ satisfying certain
  `p : Prop` gives the generating function for `#(Nat.Partition.restricted n p)`.
  (See `Nat.Partition.hasProd_powerSeriesMk_card_restricted`)

The definition of `Nat.Partition.genFun` ignores the value of $f(0, c)$ and $f(i, 0)$. The formula
can be interpreted as assuming $f(i, 0) = 1$ and $f(0, c) = 0$ for $c \ne 0$. In theory we could
respect the actual value of $f(0, c)$ and $f(i, 0)$, but it makes the otherwise finite sum and
product potentially infinite.
-/

open Finset PowerSeries

open scoped PowerSeries.WithPiTopology

namespace Nat.Partition

variable {R : Type*} [CommSemiring R]

noncomputable def genFun (f : ℕ → ℕ → R) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ ∑ p : n.Partition, p.parts.toFinsupp.prod f
