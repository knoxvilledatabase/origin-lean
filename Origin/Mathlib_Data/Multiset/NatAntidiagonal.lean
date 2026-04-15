/-
Extracted from Data/Multiset/NatAntidiagonal.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Data.Multiset.Nodup
import Mathlib.Data.List.NatAntidiagonal

/-!
# Antidiagonals in ℕ × ℕ as multisets

This file defines the antidiagonals of ℕ × ℕ as multisets: the `n`-th antidiagonal is the multiset
of pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines file `Data.List.NatAntidiagonal` and is further refined by file
`Data.Finset.NatAntidiagonal`.
-/

namespace Multiset

namespace Nat

def antidiagonal (n : ℕ) : Multiset (ℕ × ℕ) :=
  List.Nat.antidiagonal n

@[simp]
theorem mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} : x ∈ antidiagonal n ↔ x.1 + x.2 = n := by
  rw [antidiagonal, mem_coe, List.Nat.mem_antidiagonal]

@[simp]
theorem card_antidiagonal (n : ℕ) : card (antidiagonal n) = n + 1 := by
  rw [antidiagonal, coe_card, List.Nat.length_antidiagonal]

@[simp]
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
  rfl

@[simp]
theorem nodup_antidiagonal (n : ℕ) : Nodup (antidiagonal n) :=
  coe_nodup.2 <| List.Nat.nodup_antidiagonal n

@[simp]
theorem antidiagonal_succ {n : ℕ} :
    antidiagonal (n + 1) = (0, n + 1) ::ₘ (antidiagonal n).map (Prod.map Nat.succ id) := by
  simp only [antidiagonal, List.Nat.antidiagonal_succ, map_coe, cons_coe]

theorem antidiagonal_succ' {n : ℕ} :
    antidiagonal (n + 1) = (n + 1, 0) ::ₘ (antidiagonal n).map (Prod.map id Nat.succ) := by
  rw [antidiagonal, List.Nat.antidiagonal_succ', ← coe_add, add_comm, antidiagonal, map_coe,
    coe_add, List.singleton_append, cons_coe]

theorem antidiagonal_succ_succ' {n : ℕ} :
    antidiagonal (n + 2) =
      (0, n + 2) ::ₘ (n + 2, 0) ::ₘ (antidiagonal n).map (Prod.map Nat.succ Nat.succ) := by
  rw [antidiagonal_succ, antidiagonal_succ', map_cons, map_map, Prod.map_apply]
  rfl

theorem map_swap_antidiagonal {n : ℕ} : (antidiagonal n).map Prod.swap = antidiagonal n := by
  rw [antidiagonal, map_coe, List.Nat.map_swap_antidiagonal, coe_reverse]

end Nat

end Multiset
