/-
Extracted from FieldTheory/KummerPolynomial.lean
Genuine: 3 of 8 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core

/-!
# Irreducibility of X ^ p - a

## Main result
- `X_pow_sub_C_irreducible_iff_of_prime`: For `p` prime, `X ^ p - C a` is irreducible iff `a` is not
  a `p`-power. This is not true for composite `n`. For example, `x^4+4=(x^2-2x+2)(x^2+2x+2)` but
  `-4` is not a 4th power.

-/

universe u

variable {K : Type u} [Field K]

open Polynomial AdjoinRoot

section Splits

lemma root_X_pow_sub_C_pow (n : ℕ) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) ^ n = AdjoinRoot.of _ a := by
  rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root, eval₂_sub, eval₂_C, eval₂_pow, eval₂_X]

-- DISSOLVED: root_X_pow_sub_C_ne_zero

-- DISSOLVED: root_X_pow_sub_C_ne_zero'

end Splits

section Irreducible

-- DISSOLVED: ne_zero_of_irreducible_X_pow_sub_C

-- DISSOLVED: ne_zero_of_irreducible_X_pow_sub_C'

lemma root_X_pow_sub_C_eq_zero_iff {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    (AdjoinRoot.root (X ^ n - C a)) = 0 ↔ a = 0 := by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  refine ⟨not_imp_not.mp (root_X_pow_sub_C_ne_zero' hn), ?_⟩
  rintro rfl
  have := not_imp_not.mp (fun hn ↦ ne_zero_of_irreducible_X_pow_sub_C' hn H) rfl
  rw [this, pow_one, map_zero, sub_zero, ← mk_X, mk_self]

-- DISSOLVED: root_X_pow_sub_C_ne_zero_iff

theorem pow_ne_of_irreducible_X_pow_sub_C {n : ℕ} {a : K}
    (H : Irreducible (X ^ n - C a)) {m : ℕ} (hm : m ∣ n) (hm' : m ≠ 1) (b : K) : b ^ m ≠ a := by
  have hn : n ≠ 0 := fun e ↦ not_irreducible_C
    (1 - a) (by simpa only [e, pow_zero, ← C.map_one, ← map_sub] using H)
  obtain ⟨k, rfl⟩ := hm
  rintro rfl
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X ^ k) (C b) m
  rw [mul_comm, pow_mul, map_pow, hq] at H
  have : degree q = 0 := by
    simpa [isUnit_iff_degree_eq_zero, degree_X_pow_sub_C,
      Nat.pos_iff_ne_zero, (mul_ne_zero_iff.mp hn).2] using H.2 rfl
  apply_fun degree at hq
  simp only [this, ← pow_mul, mul_comm k m, degree_X_pow_sub_C, Nat.pos_iff_ne_zero.mpr hn,
    Nat.pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).2, degree_mul, ← map_pow, add_zero,
    Nat.cast_injective.eq_iff] at hq
  exact hm' ((mul_eq_right₀ (mul_ne_zero_iff.mp hn).2).mp hq)
