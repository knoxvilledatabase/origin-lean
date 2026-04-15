/-
Extracted from Algebra/GCDMonoid/Multiset.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# GCD and LCM operations on multisets

## Main definitions

- `Multiset.gcd` - the greatest common denominator of a `Multiset` of elements of a `GCDMonoid`
- `Multiset.lcm` - the least common multiple of a `Multiset` of elements of a `GCDMonoid`

## Implementation notes

TODO: simplify with a tactic and `Data.Multiset.Lattice`

## Tags

multiset, gcd
-/

namespace Multiset

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### LCM -/

section lcm

def lcm (s : Multiset α) : α :=
  s.fold GCDMonoid.lcm 1
