/-
Extracted from Data/Nat/Prime/Infinite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Bounds.Basic

/-!
## Notable Theorems

- `Nat.exists_infinite_primes`: Euclid's theorem that there exist infinitely many prime numbers.
  This also appears as `Nat.not_bddAbove_setOf_prime` and `Nat.infinite_setOf_prime` (the latter
  in `Data.Nat.PrimeFin`).

-/

open Bool Subtype

open Nat

namespace Nat

section Infinite

theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Prime p :=
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Prime p := minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩

theorem not_bddAbove_setOf_prime : ¬BddAbove { p | Prime p } := by
  rw [not_bddAbove_iff]
  intro n
  obtain ⟨p, hi, hp⟩ := exists_infinite_primes n.succ
  exact ⟨p, hp, hi⟩

end Infinite

end Nat
