/-
Extracted from Data/Fin/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The finite type with `n` elements

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

* `finZeroElim` : Elimination principle for the empty set `Fin 0`, generalizes `Fin.elim0`.
Further definitions and eliminators can be found in `Init.Data.Fin.Lemmas`
* `Fin.equivSubtype` : Equivalence between `Fin n` and `{ i // i < n }`.

-/

assert_not_exists Monoid Finset

open Fin Nat Function

attribute [simp] Fin.succ_ne_zero Fin.castSucc_lt_last

theorem Nat.forall_lt_iff_fin {n : ℕ} {p : ∀ k, k < n → Prop} :
    (∀ k hk, p k hk) ↔ ∀ k : Fin n, p k k.is_lt :=
  .symm <| Fin.forall_iff

theorem Nat.exists_lt_iff_fin {n : ℕ} {p : ∀ k, k < n → Prop} :
    (∃ k hk, p k hk) ↔ ∃ k : Fin n, p k k.is_lt :=
  .symm <| Fin.exists_iff

def finZeroElim {α : Fin 0 → Sort*} (x : Fin 0) : α x :=
  x.elim0

namespace Fin
