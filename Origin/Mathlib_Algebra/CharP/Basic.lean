/-
Extracted from Algebra/CharP/Basic.lean
Genuine: 11 of 21 | Dissolved: 4 | Infrastructure: 6
-/
import Origin.Core

/-!
# Characteristic of semirings

This file collects some fundamental results on the characteristic of rings that don't need the extra
imports of `Mathlib/Algebra/CharP/Lemmas.lean`.

As such, we can probably reorganize and find a better home for most of these lemmas.
-/

assert_not_exists Finset TwoSidedIdeal

open Set

variable (R : Type*)

namespace CharP

section AddMonoidWithOne

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

lemma natCast_eq_natCast' (h : a ≡ b [MOD p]) : (a : R) = b := by
  wlog hle : a ≤ b
  · exact (this R p h.symm (le_of_not_ge hle)).symm
  rw [Nat.modEq_iff_dvd' hle] at h
  rw [← Nat.sub_add_cancel hle, Nat.cast_add, (cast_eq_zero_iff R p _).mpr h, zero_add]

lemma natCast_eq_natCast_mod (a : ℕ) : (a : R) = a % p :=
  natCast_eq_natCast' R p (Nat.mod_modEq a p).symm

variable [IsRightCancelAdd R]

lemma natCast_eq_natCast : (a : R) = b ↔ a ≡ b [MOD p] := by
  wlog hle : a ≤ b
  · rw [eq_comm, this R p (le_of_not_ge hle), Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' hle, ← cast_eq_zero_iff R p (b - a),
    ← add_right_cancel_iff (G := R) (a := a) (b := b - a), zero_add, ← Nat.cast_add,
    Nat.sub_add_cancel hle, eq_comm]

lemma natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : ℕ → R) :=
  fun _a ha _b hb hab ↦ ((natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb

end AddMonoidWithOne

section AddGroupWithOne

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

lemma intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD p] := by
  rw [eq_comm, ← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff R p, Int.modEq_iff_dvd]

lemma intCast_eq_intCast_mod : (a : R) = a % (p : ℤ) :=
  (CharP.intCast_eq_intCast R p).mpr (Int.mod_modEq a p).symm

lemma intCast_injOn_Ico [IsRightCancelAdd R] : InjOn (Int.cast : ℤ → R) (Ico 0 p) := by
  rintro a ⟨ha₀, ha⟩ b ⟨hb₀, hb⟩ hab
  lift a to ℕ using ha₀
  lift b to ℕ using hb₀
  norm_cast at *
  exact natCast_injOn_Iio _ _ ha hb hab

end AddGroupWithOne

end CharP

namespace CharP

section NonAssocSemiring

variable {R} [NonAssocSemiring R]

variable (R) in

-- DISSOLVED: cast_ne_zero_of_ne_of_prime

lemma ringChar_of_prime_eq_zero [Nontrivial R] {p : ℕ} (hprime : Nat.Prime p)
    (hp0 : (p : R) = 0) : ringChar R = p :=
  Or.resolve_left ((Nat.dvd_prime hprime).1 (ringChar.dvd hp0)) ringChar_ne_one

lemma charP_iff_prime_eq_zero [Nontrivial R] {p : ℕ} (hp : p.Prime) :
    CharP R p ↔ (p : R) = 0 :=
  ⟨fun _ => cast_eq_zero R p,
   fun hp0 => (ringChar_of_prime_eq_zero hp hp0) ▸ inferInstance⟩

end NonAssocSemiring

end CharP

-- DISSOLVED: Ring.two_ne_zero

-- DISSOLVED: Ring.neg_one_ne_one_of_char_ne_two

lemma Ring.eq_self_iff_eq_zero_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    [NoZeroDivisors R] (hR : ringChar R ≠ 2) {a : R} : -a = a ↔ a = 0 :=
  ⟨fun h =>
    (mul_eq_zero.mp <| (two_mul a).trans <| neg_eq_iff_add_eq_zero.mp h).resolve_left
      (Ring.two_ne_zero hR),
    fun h => ((congr_arg (fun x => -x) h).trans neg_zero).trans h.symm⟩

end

section Prod

variable (S : Type*) [AddMonoidWithOne R] [AddMonoidWithOne S] (p q : ℕ) [CharP R p]

-- INSTANCE (free from Core): Nat.lcm.charP

-- INSTANCE (free from Core): Prod.charP

-- INSTANCE (free from Core): Prod.charZero_of_left

-- INSTANCE (free from Core): Prod.charZero_of_right

end Prod

-- INSTANCE (free from Core): ULift.charP

-- INSTANCE (free from Core): MulOpposite.charP

lemma Int.cast_injOn_of_ringChar_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : ({0, 1, -1} : Set ℤ).InjOn ((↑) : ℤ → R) := by
  rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) h <;>
  simp only
    [cast_neg, cast_one, cast_zero, neg_eq_zero, one_ne_zero, zero_ne_one, zero_eq_neg] at h ⊢
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR).symm h).elim
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR) h).elim

end

namespace CharZero

-- DISSOLVED: charZero_iff_forall_prime_ne_zero

end CharZero

namespace Fin

open Fin.NatCast
