/-
Extracted from Computability/Ackermann.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ackermann function

In this file, we define the two-argument Ackermann function `ack`. Despite having a recursive
definition, we show that this isn't a primitive recursive function.

## Main results

- `exists_lt_ack_of_nat_primrec`: any primitive recursive function is pointwise bounded above by
  `ack m` for some `m`.
- `not_primrec₂_ack`: the two-argument Ackermann function is not primitive recursive.
- `computable₂_ack`: the two-argument Ackermann function is computable.

## Proof approach

We very broadly adapt the proof idea from
https://www.planetmath.org/ackermannfunctionisnotprimitiverecursive. Namely, we prove that for any
primitive recursive `f : ℕ → ℕ`, there exists `m` such that `f n < ack m n` for all `n`. This then
implies that `fun n => ack n n` can't be primitive recursive, and so neither can `ack`. We aren't
able to use the same bounds as in that proof though, since our approach of using pairing functions
differs from their approach of using multivariate functions.

The important bounds we show during the main inductive proof (`exists_lt_ack_of_nat_primrec`)
are the following. Assuming `∀ n, f n < ack a n` and `∀ n, g n < ack b n`, we have:

- `∀ n, pair (f n) (g n) < ack (max a b + 3) n`.
- `∀ n, g (f n) < ack (max a b + 2) n`.
- `∀ n, Nat.rec (f n.unpair.1) (fun (y IH : ℕ) => g (pair n.unpair.1 (pair y IH)))
  n.unpair.2 < ack (max a b + 9) n`.

The last one is evidently the hardest. Using `unpair_add_le`, we reduce it to the more manageable

- `∀ m n, rec (f m) (fun (y IH : ℕ) => g (pair m (pair y IH))) n <
  ack (max a b + 9) (m + n)`.

We then prove this by induction on `n`. Our proof crucially depends on `ack_pair_lt`, which is
applied twice, giving us a constant of `4 + 4`. The rest of the proof consists of simpler bounds
which bump up our constant to `9`.
-/

open Nat

def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
