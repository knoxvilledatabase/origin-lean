/-
Extracted from Logic/Equiv/Fin/Rotate.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cyclic permutations on `Fin n`

This file defines
* `finRotate`, which corresponds to the cycle `(1, ..., n)` on `Fin n`
* `finCycle`, the permutation that adds a fixed number to each element of `Fin n`
and proves various lemmas about them.
-/

open Nat

variable {n : ℕ}

def finRotate : ∀ n, Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | n + 1 => finAddFlip.trans (finCongr (Nat.add_comm 1 n))
