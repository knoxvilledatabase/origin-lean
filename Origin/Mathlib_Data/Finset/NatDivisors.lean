/-
Extracted from Data/Finset/NatDivisors.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `Nat.divisors` as a multiplicative homomorphism

The main definition of this file is `Nat.divisorsHom : ℕ →* Finset ℕ`,
exhibiting `Nat.divisors` as a multiplicative homomorphism from `ℕ` to `Finset ℕ`.
-/

open Nat Finset

open scoped Pointwise

lemma Nat.divisors_mul (m n : ℕ) : divisors (m * n) = divisors m * divisors n := by
  ext k
  simp_rw [mem_mul, mem_divisors, Nat.dvd_mul, mul_ne_zero_iff, ← exists_and_left,
    ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]
