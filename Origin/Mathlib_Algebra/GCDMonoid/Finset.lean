/-
Extracted from Algebra/GCDMonoid/Finset.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# GCD and LCM operations on finsets

## Main definitions

- `Finset.gcd` - the greatest common denominator of a `Finset` of elements of a `GCDMonoid`
- `Finset.lcm` - the least common multiple of a `Finset` of elements of a `GCDMonoid`

## Implementation notes

Many of the proofs use the lemmas `gcd_def` and `lcm_def`, which relate `Finset.gcd`
and `Finset.lcm` to `Multiset.gcd` and `Multiset.lcm`.

TODO: simplify with a tactic and `Data.Finset.Lattice`

## Tags

finset, gcd
-/

variable {ι α β γ : Type*}

namespace Finset

open Multiset

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### lcm -/

section lcm

def lcm (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.lcm 1 f

variable {s s₁ s₂ : Finset β} {f : β → α}
