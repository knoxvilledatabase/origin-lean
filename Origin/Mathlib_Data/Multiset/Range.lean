/-
Extracted from Data/Multiset/Range.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # `Multiset.range n` gives `{0, 1, ..., n-1}` as a multiset. -/

assert_not_exists Monoid

open List Nat

namespace Multiset

def range (n : ℕ) : Multiset ℕ :=
  List.range n
