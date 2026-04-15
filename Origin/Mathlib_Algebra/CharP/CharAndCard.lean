/-
Extracted from Algebra/CharP/CharAndCard.lean
Genuine: 4 | Conflates: 0 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Characteristic and cardinality

We prove some results relating characteristic and cardinality of finite rings

## Tags
characteristic, cardinality, ring
-/

-- DISSOLVED: isUnit_iff_not_dvd_char_of_ringChar_ne_zero

theorem isUnit_iff_not_dvd_char (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Finite R] :
    IsUnit (p : R) ↔ ¬p ∣ ringChar R :=
  isUnit_iff_not_dvd_char_of_ringChar_ne_zero R p <| CharP.char_ne_zero_of_finite R (ringChar R)

theorem prime_dvd_char_iff_dvd_card {R : Type*} [CommRing R] [Fintype R] (p : ℕ) [Fact p.Prime] :
    p ∣ ringChar R ↔ p ∣ Fintype.card R := by
  refine
    ⟨fun h =>
      h.trans <|
        Int.natCast_dvd_natCast.mp <|
          (CharP.intCast_eq_zero_iff R (ringChar R) (Fintype.card R)).mp <|
            mod_cast Nat.cast_card_eq_zero R,
      fun h => ?_⟩
  by_contra h₀
  rcases exists_prime_addOrderOf_dvd_card p h with ⟨r, hr⟩
  have hr₁ := addOrderOf_nsmul_eq_zero r
  rw [hr, nsmul_eq_mul] at hr₁
  rcases IsUnit.exists_left_inv ((isUnit_iff_not_dvd_char R p).mpr h₀) with ⟨u, hu⟩
  apply_fun (· * ·) u at hr₁
  rw [mul_zero, ← mul_assoc, hu, one_mul] at hr₁
  exact mt AddMonoid.addOrderOf_eq_one_iff.mpr (ne_of_eq_of_ne hr (Nat.Prime.ne_one Fact.out)) hr₁

theorem not_isUnit_prime_of_dvd_card {R : Type*} [CommRing R] [Fintype R] (p : ℕ) [Fact p.Prime]
    (hp : p ∣ Fintype.card R) : ¬IsUnit (p : R) :=
  mt (isUnit_iff_not_dvd_char R p).mp
    (Classical.not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))

lemma charP_of_card_eq_prime {R : Type*} [NonAssocRing R] [Fintype R] (p : ℕ) [hp : Fact p.Prime]
    (hR : Fintype.card R = p) : CharP R p :=
  have := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.1.one_lt)
  (CharP.charP_iff_prime_eq_zero hp.1).2 (hR ▸ Nat.cast_card_eq_zero R)
