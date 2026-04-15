/-
Extracted from Data/Fin/SuccPred.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Successors and predecessor operations of `Fin n`

This file contains a number of definitions and lemmas
related to `Fin.succ`, `Fin.pred`, and related operations on `Fin n`.

## Main definitions

* `finCongr` : `Fin.cast` as an `Equiv`, equivalence between `Fin n` and `Fin m` when `n = m`;
* `Fin.succAbove` : embeds `Fin n` into `Fin (n + 1)` skipping `p`.
* `Fin.predAbove` : the (partial) inverse of `Fin.succAbove`.

-/

assert_not_exists Monoid Finset

open Fin Nat Function

attribute [simp] Fin.succ_ne_zero Fin.castSucc_lt_last

namespace Fin

variable {n m : ℕ}

section Succ

/-!
### succ and casts into larger Fin types
-/

lemma succ_injective (n : ℕ) : Injective (@Fin.succ n) := fun a b ↦ by simp [Fin.ext_iff]
