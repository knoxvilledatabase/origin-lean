/-
Extracted from Data/Int/Lemmas.lean
Genuine: 15 of 15 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Miscellaneous lemmas about the integers

This file contains lemmas about integers, which require further imports than
`Data.Int.Basic` or `Data.Int.Order`.

-/

open Nat

namespace Int

theorem le_natCast_sub (m n : ℕ) : (m - n : ℤ) ≤ ↑(m - n : ℕ) := by
  lia

/-! ### `succ` and `pred` -/

theorem succ_natCast_pos (n : ℕ) : 0 < (n : ℤ) + 1 :=
  lt_add_one_iff.mpr (by simp)

/-! ### `natAbs` -/

theorem natAbs_eq_iff_sq_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a ^ 2 = b ^ 2 := by
  rw [sq, sq]
  exact natAbs_eq_iff_mul_self_eq

theorem natAbs_lt_iff_sq_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a ^ 2 < b ^ 2 := by
  rw [sq, sq]
  exact natAbs_lt_iff_mul_self_lt

theorem natAbs_le_iff_sq_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a ^ 2 ≤ b ^ 2 := by
  rw [sq, sq]
  exact natAbs_le_iff_mul_self_le

theorem natAbs_inj_of_nonneg_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    natAbs a = natAbs b ↔ a = b := by rw [← sq_eq_sq₀ ha hb, ← natAbs_eq_iff_sq_eq]

theorem natAbs_inj_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) :
    natAbs a = natAbs b ↔ a = b := by
  simpa only [Int.natAbs_neg, neg_inj] using
    natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)

theorem natAbs_inj_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) :
    natAbs a = natAbs b ↔ a = -b := by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg ha (neg_nonneg_of_nonpos hb)

theorem natAbs_inj_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    natAbs a = natAbs b ↔ -a = b := by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) hb

theorem natAbs_coe_sub_coe_le_of_le {a b n : ℕ} (a_le_n : a ≤ n) (b_le_n : b ≤ n) :
    natAbs (a - b : ℤ) ≤ n := by
  rw [← Nat.cast_le (α := ℤ), natCast_natAbs]
  exact abs_sub_le_of_nonneg_of_le (natCast_nonneg a) (ofNat_le.mpr a_le_n)
    (natCast_nonneg b) (ofNat_le.mpr b_le_n)

theorem natAbs_coe_sub_coe_lt_of_lt {a b n : ℕ} (a_lt_n : a < n) (b_lt_n : b < n) :
    natAbs (a - b : ℤ) < n := by
  rw [← Nat.cast_lt (α := ℤ), natCast_natAbs]
  exact abs_sub_lt_of_nonneg_of_lt (natCast_nonneg a) (ofNat_lt.mpr a_lt_n)
    (natCast_nonneg b) (ofNat_lt.mpr b_lt_n)

section Intervals

open Set

theorem strictMonoOn_natAbs : StrictMonoOn natAbs (Ici 0) := fun _ ha _ _ hab =>
  natAbs_lt_natAbs_of_nonneg_of_lt ha hab

theorem strictAntiOn_natAbs : StrictAntiOn natAbs (Iic 0) := fun a _ b hb hab => by
  simpa [Int.natAbs_neg] using
    natAbs_lt_natAbs_of_nonneg_of_lt (Right.nonneg_neg_iff.mpr hb) (neg_lt_neg_iff.mpr hab)

theorem injOn_natAbs_Ici : InjOn natAbs (Ici 0) :=
  strictMonoOn_natAbs.injOn

theorem injOn_natAbs_Iic : InjOn natAbs (Iic 0) :=
  strictAntiOn_natAbs.injOn

end Intervals

/-! ### bitwise ops

This lemma is orphaned from `Data.Int.Bitwise` as it also requires material from `Data.Int.Order`.
-/
