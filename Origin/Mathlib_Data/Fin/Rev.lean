/-
Extracted from Data/Fin/Rev.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Reverse on `Fin n`

This file contains lemmas about `Fin.rev : Fin n → Fin n` which maps `i` to `n - 1 - i`.

## Definitions

* `Fin.revPerm : Equiv.Perm (Fin n)` : `Fin.rev` as an `Equiv.Perm`, the antitone involution given
  by `i ↦ n-(i+1)`
-/

assert_not_exists Monoid Fintype

open Fin Nat Function

namespace Fin

variable {n m : ℕ}

theorem rev_involutive : Involutive (rev : Fin n → Fin n) := rev_rev
