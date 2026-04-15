/-
Extracted from Order/Interval/Finset/Nat.lean
Genuine: 1 of 8 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Finite intervals of naturals

This file proves that `ℕ` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

Some lemmas can be generalized using `OrderedGroup`, `CanonicallyOrderedMul` or `SuccOrder`
and subsequently be moved upstream to `Order.Interval.Finset`.
-/

assert_not_exists Ring

open Finset Nat

variable (a b c : ℕ)

namespace Nat

-- INSTANCE (free from Core): instLocallyFiniteOrder

-- INSTANCE (free from Core): :

theorem Iio_eq_range : Iio a = range a := by
  grind
