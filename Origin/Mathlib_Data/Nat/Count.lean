/-
Extracted from Data/Nat/Count.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Counting on ℕ

This file defines the `count` function, which gives, for any predicate on the natural numbers,
"how many numbers under `k` satisfy this predicate?".
We then prove several expected lemmas about `count`, relating it to the cardinality of other
objects, and helping to evaluate it for specific `k`.

-/

assert_not_imported Mathlib.Dynamics.FixedPoints.Basic

assert_not_exists Ring

open Finset

namespace Nat

variable (p : ℕ → Prop)

section Count

variable [DecidablePred p]

def count (n : ℕ) : ℕ :=
  (List.range n).countP p
