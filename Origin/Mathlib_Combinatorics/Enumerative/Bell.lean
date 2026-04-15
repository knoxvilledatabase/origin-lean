/-
Extracted from Combinatorics/Enumerative/Bell.lean
Genuine: 10 | Conflates: 0 | Dissolved: 3 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Mul

/-! # Bell numbers for multisets

For `n : ℕ`, the `n`th Bell number is the number of partitions of a set of cardinality `n`.
Here, we define a refinement of these numbers, that count, for any `m : Multiset ℕ`,
the number of partitions of a set of cardinality `m.sum` whose parts have cardinalities
given by `m`.

The definition presents it as a natural number.

* `Multiset.bell`: number of partitions of a set whose parts have cardinalities a given multiset

* `Nat.uniformBell m n` : short name for `Multiset.bell (replicate m n)`

* `Multiset.bell_mul_eq` shows that
    `m.bell * (m.map (fun j ↦ j !)).prod *
      Π j ∈ (m.toFinset.erase 0), (m.count j)! = m.sum !`

* `Nat.uniformBell_mul_eq`  shows that
    `uniformBell m n * n ! ^ m * m ! = (m * n)!`

* `Nat.uniformBell_succ_left` computes `Nat.uniformBell (m + 1) n` from `Nat.uniformBell m n`

## TODO

Prove that it actually counts the number of partitions as indicated.
(When `m` contains `0`, the result requires to admit repetitions of the empty set as a part.)

-/

open Multiset Nat

namespace Multiset

def bell (m : Multiset ℕ) : ℕ :=
  Nat.multinomial m.toFinset (fun k ↦ k * m.count k) *
    ∏ k ∈ m.toFinset.erase 0, ∏ j ∈ .range (m.count k), (j * k + k - 1).choose (k - 1)

@[simp]
theorem bell_zero : bell 0 = 1 := rfl

-- DISSOLVED: bell_mul_eq_lemma

theorem bell_mul_eq (m : Multiset ℕ) :
    m.bell * (m.map (fun j ↦ j !)).prod * ∏ j ∈ (m.toFinset.erase 0), (m.count j)!
      = m.sum ! := by
  unfold bell
  rw [← Nat.mul_right_inj (a := ∏ i ∈ m.toFinset, (i * count i m)!) (by positivity)]
  simp only [← mul_assoc]
  rw [Nat.multinomial_spec]
  simp only [mul_assoc]
  rw [mul_comm]
  apply congr_arg₂
  · rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_multiset_map_count]
    suffices this : _ by
      by_cases hm : 0 ∈ m.toFinset
      · rw [← Finset.prod_erase_mul _ _ hm]
        rw [← Finset.prod_erase_mul _ _ hm]
        simp only [factorial_zero, one_pow, mul_one, zero_mul]
        exact this
      · nth_rewrite 1 [← Finset.erase_eq_of_not_mem hm]
        nth_rewrite 3 [← Finset.erase_eq_of_not_mem hm]
        exact this
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x hx
    rw [← mul_assoc, bell_mul_eq_lemma]
    simp only [Finset.mem_erase, ne_eq, mem_toFinset] at hx
    simp only [ne_eq, hx.1, not_false_eq_true]
  · apply congr_arg
    rw [Finset.sum_multiset_count]
    simp only [smul_eq_mul, mul_comm]

theorem bell_eq (m : Multiset ℕ) :
    m.bell = m.sum ! / ((m.map (fun j ↦ j !)).prod *
      ∏ j ∈ (m.toFinset.erase 0), (m.count j)!) := by
  rw [← Nat.mul_left_inj, Nat.div_mul_cancel _]
  · rw [← mul_assoc]
    exact bell_mul_eq m
  · rw [← bell_mul_eq, mul_assoc]
    apply Nat.dvd_mul_left
  · rw [← Nat.pos_iff_ne_zero]
    apply Nat.mul_pos
    · simp only [gt_iff_lt, CanonicallyOrderedCommSemiring.multiset_prod_pos, mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun _ _ ↦ Nat.factorial_pos _
    · apply Finset.prod_pos
      exact fun _ _ ↦ Nat.factorial_pos _

end Multiset

namespace Nat

def uniformBell (m n : ℕ) : ℕ := bell (replicate m n)

theorem uniformBell_eq (m n : ℕ) : m.uniformBell n =
    ∏ p ∈ (Finset.range m), Nat.choose (p * n + n - 1) (n - 1) := by
  unfold uniformBell bell
  rw [toFinset_replicate]
  split_ifs with hm
  · simp  [hm]
  · by_cases hn : n = 0
    · simp [hn]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp [count_replicate]

theorem uniformBell_zero_left (n : ℕ) : uniformBell 0 n = 1 := by
  simp [uniformBell_eq]

theorem uniformBell_zero_right (m : ℕ) : uniformBell m 0 = 1 := by
  simp [uniformBell_eq]

theorem uniformBell_succ_left (m n : ℕ) :
    uniformBell (m+1) n = choose (m * n + n - 1) (n - 1) * uniformBell m n := by
  simp only [uniformBell_eq, Finset.prod_range_succ, mul_comm]

theorem uniformBell_one_left (n : ℕ) : uniformBell 1 n = 1 := by
  simp only [uniformBell_eq, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]

theorem uniformBell_one_right (m : ℕ) : uniformBell m 1 = 1 := by
  simp only [uniformBell_eq, mul_one, add_tsub_cancel_right, ge_iff_le, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]

-- DISSOLVED: uniformBell_mul_eq

-- DISSOLVED: uniformBell_eq_div

end Nat
