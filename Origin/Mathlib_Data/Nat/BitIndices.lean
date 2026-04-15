/-
Extracted from Data/Nat/BitIndices.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bit Indices

Given `n : ℕ`, we define `Nat.bitIndices n`, which is the `List` of indices of `1`s in the
binary expansion of `n`. If `s : Finset ℕ` and `n = ∑ i ∈ s, 2 ^ i`, then
`Nat.bitIndices n` is the sorted list of elements of `s`.

The lemma `twoPowSum_bitIndices` proves that summing `2 ^ i` over this list gives `n`.
This is used in `Combinatorics.colex` to construct a bijection `equivBitIndices : ℕ ≃ Finset ℕ`.

## TODO

Relate the material in this file to `Nat.digits` and `Nat.bits`.
-/

open List

namespace Nat

variable {a n : ℕ}

def bitIndices (n : ℕ) : List ℕ :=
  @binaryRec (fun _ ↦ List ℕ) [] (fun b _ s ↦ b.casesOn (s.map (· + 1)) (0 :: s.map (· + 1))) n
