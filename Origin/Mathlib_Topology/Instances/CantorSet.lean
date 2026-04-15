/-
Extracted from Topology/Instances/CantorSet.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ternary Cantor Set

This file defines the Cantor ternary set and proves a few properties.

## Main Definitions

* `preCantorSet n`: The order `n` pre-Cantor set, defined inductively as the union of the images
  under the functions `(· / 3)` and `((2 + ·) / 3)`, with `preCantorSet 0 := Set.Icc 0 1`, i.e.
  `preCantorSet 0` is the unit interval [0,1].
* `cantorSet`: The ternary Cantor set, defined as the intersection of all pre-Cantor sets.
* `cantorToTernary`: given a number `x` in the Cantor set, returns its ternary representation
  `(d₀, d₁, ...)` consisting only of digits `0` and `2`, such that `x = 0.d₀d₁...`
  (see `ofDigits_cantorToTernary`).
* `ofDigits_zero_two_sequence_mem_cantorSet`: any such sequence corresponds to a number
  in the Cantor set.
* `ofDigits_zero_two_sequence_unique`: such a representation is unique.
-/

def preCantorSet : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | n + 1 => (· / 3) '' preCantorSet n ∪ (fun x ↦ (2 + x) / 3) '' preCantorSet n
