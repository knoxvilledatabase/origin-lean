/-
Extracted from Algebra/Squarefree/Basic.lean
Genuine: 25 of 35 | Dissolved: 9 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Squarefree elements of monoids
An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

Results about squarefree natural numbers are proved in `Data.Nat.Squarefree`.

## Main Definitions
 - `Squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
 - `multiplicity.squarefree_iff_emultiplicity_le_one`: `x` is `Squarefree` iff for every `y`, either
  `emultiplicity y x ≤ 1` or `IsUnit y`.
 - `UniqueFactorizationMonoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
 factorization monoid is squarefree iff `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/

variable {R : Type*}

def Squarefree [Monoid R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x

theorem IsRelPrime.of_squarefree_mul [CommMonoid R] {m n : R} (h : Squarefree (m * n)) :
    IsRelPrime m n := fun c hca hcb ↦ h c (mul_dvd_mul hca hcb)

@[simp]
theorem IsUnit.squarefree [CommMonoid R] {x : R} (h : IsUnit x) : Squarefree x := fun _ hdvd =>
  isUnit_of_mul_isUnit_left (isUnit_of_dvd_unit hdvd h)

theorem squarefree_one [CommMonoid R] : Squarefree (1 : R) :=
  isUnit_one.squarefree

@[simp]
theorem not_squarefree_zero [MonoidWithZero R] [Nontrivial R] : ¬Squarefree (0 : R) := by
  erw [not_forall]
  exact ⟨0, by simp⟩

-- DISSOLVED: Squarefree.ne_zero

@[simp]
theorem Irreducible.squarefree [CommMonoid R] {x : R} (h : Irreducible x) : Squarefree x := by
  rintro y ⟨z, hz⟩
  rw [mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact hu
  · apply isUnit_of_mul_isUnit_left hu

@[simp]
theorem Prime.squarefree [CancelCommMonoidWithZero R] {x : R} (h : Prime x) : Squarefree x :=
  h.irreducible.squarefree

theorem Squarefree.of_mul_left [Monoid R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree m :=
  fun p hp => hmn p (dvd_mul_of_dvd_left hp n)

theorem Squarefree.of_mul_right [CommMonoid R] {m n : R} (hmn : Squarefree (m * n)) :
    Squarefree n := fun p hp => hmn p (dvd_mul_of_dvd_right hp m)

theorem Squarefree.squarefree_of_dvd [Monoid R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) :
    Squarefree x := fun _ h => hsq _ (h.trans hdvd)

theorem Squarefree.eq_zero_or_one_of_pow_of_not_isUnit [Monoid R] {x : R} {n : ℕ}
    (h : Squarefree (x ^ n)) (h' : ¬ IsUnit x) :
    n = 0 ∨ n = 1 := by
  contrapose! h'
  replace h' : 2 ≤ n := by omega
  have : x * x ∣ x ^ n := by rw [← sq]; exact pow_dvd_pow x h'
  exact h.squarefree_of_dvd this x (refl _)

theorem Squarefree.pow_dvd_of_pow_dvd [Monoid R] {x y : R} {n : ℕ}
    (hx : Squarefree y) (h : x ^ n ∣ y) : x ^ n ∣ x := by
  by_cases hu : IsUnit x
  · exact (hu.pow n).dvd
  · rcases (hx.squarefree_of_dvd h).eq_zero_or_one_of_pow_of_not_isUnit hu with rfl | rfl <;> simp

section SquarefreeGcdOfSquarefree

variable {α : Type*} [CancelCommMonoidWithZero α] [GCDMonoid α]

theorem Squarefree.gcd_right (a : α) {b : α} (hb : Squarefree b) : Squarefree (gcd a b) :=
  hb.squarefree_of_dvd (gcd_dvd_right _ _)

theorem Squarefree.gcd_left {a : α} (b : α) (ha : Squarefree a) : Squarefree (gcd a b) :=
  ha.squarefree_of_dvd (gcd_dvd_left _ _)

end SquarefreeGcdOfSquarefree

namespace multiplicity

section CommMonoid

variable [CommMonoid R]

theorem squarefree_iff_emultiplicity_le_one (r : R) :
    Squarefree r ↔ ∀ x : R, emultiplicity x r ≤ 1 ∨ IsUnit x := by
  refine forall_congr' fun a => ?_
  rw [← sq, pow_dvd_iff_le_emultiplicity, or_iff_not_imp_left, not_le, imp_congr _ Iff.rfl]
  norm_cast
  rw [← one_add_one_eq_two]
  exact Order.add_one_le_iff_of_not_isMax (by simp)

end CommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero R] [WfDvdMonoid R]

-- DISSOLVED: finite_prime_left

end CancelCommMonoidWithZero

end multiplicity

section Irreducible

variable [CommMonoidWithZero R] [WfDvdMonoid R]

-- DISSOLVED: squarefree_iff_no_irreducibles

theorem irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) :
    (∀ x : R, Irreducible x → ¬x * x ∣ r) ↔ (r = 0 ∧ ∀ x : R, ¬Irreducible x) ∨ Squarefree r := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases eq_or_ne r 0 with (rfl | hr)
    · exact .inl (by simpa using h)
    · exact .inr ((squarefree_iff_no_irreducibles hr).mpr h)
  · rintro (⟨rfl, h⟩ | h)
    · simpa using h
    intro x hx t
    exact hx.not_unit (h x t)

-- DISSOLVED: squarefree_iff_irreducible_sq_not_dvd_of_ne_zero

theorem squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R}
    (hr : ∃ x : R, Irreducible x) : Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree, ← not_exists]
  simp only [hr, not_true, false_or, and_false]

end Irreducible

section IsRadical

section

variable [CommMonoidWithZero R] [DecompositionMonoid R]

theorem Squarefree.isRadical {x : R} (hx : Squarefree x) : IsRadical x :=
  (isRadical_iff_pow_one_lt 2 one_lt_two).2 fun y hy ↦ by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (sq y ▸ hy)
    exact (IsRelPrime.of_squarefree_mul hx).mul_dvd ha hb

-- DISSOLVED: Squarefree.dvd_pow_iff_dvd

alias UniqueFactorizationMonoid.dvd_pow_iff_dvd_of_squarefree := Squarefree.dvd_pow_iff_dvd

end

variable [CancelCommMonoidWithZero R] {x y p d : R}

-- DISSOLVED: IsRadical.squarefree

namespace Squarefree

theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right {k : ℕ}
    (hx : Squarefree x) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ y := by
  by_cases hxp : p ∣ x
  · obtain ⟨x', rfl⟩ := hxp
    have hx' : ¬ p ∣ x' := fun contra ↦ hp.not_unit <| hx p (mul_dvd_mul_left p contra)
    replace h : p ^ k ∣ x' * y := by
      rw [pow_succ', mul_assoc] at h
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp h
    exact hp.pow_dvd_of_dvd_mul_left _ hx' h
  · exact (pow_dvd_pow _ k.le_succ).trans (hp.pow_dvd_of_dvd_mul_left _ hxp h)

theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left {k : ℕ}
    (hy : Squarefree y) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ x := by
  rw [mul_comm] at h
  exact pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hy hp h

variable [DecompositionMonoid R]

theorem dvd_of_squarefree_of_mul_dvd_mul_right (hx : Squarefree x) (h : d * d ∣ x * y) : d ∣ y := by
  nontriviality R
  obtain ⟨a, b, ha, hb, eq⟩ := exists_dvd_and_dvd_of_dvd_mul h
  replace ha : Squarefree a := hx.squarefree_of_dvd ha
  obtain ⟨c, hc⟩ : a ∣ d := ha.isRadical 2 d ⟨b, by rw [sq, eq]⟩
  rw [hc, mul_assoc, (mul_right_injective₀ ha.ne_zero).eq_iff] at eq
  exact dvd_trans ⟨c, by rw [hc, ← eq, mul_comm]⟩ hb

theorem dvd_of_squarefree_of_mul_dvd_mul_left (hy : Squarefree y) (h : d * d ∣ x * y) : d ∣ x :=
  dvd_of_squarefree_of_mul_dvd_mul_right hy (mul_comm x y ▸ h)

end Squarefree

variable [DecompositionMonoid R]

theorem squarefree_mul_iff : Squarefree (x * y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y :=
  ⟨fun h ↦ ⟨IsRelPrime.of_squarefree_mul h, h.of_mul_left, h.of_mul_right⟩,
    fun ⟨hp, sqx, sqy⟩ _ dvd ↦ hp (sqy.dvd_of_squarefree_of_mul_dvd_mul_left dvd)
      (sqx.dvd_of_squarefree_of_mul_dvd_mul_right dvd)⟩

theorem isRadical_iff_squarefree_or_zero : IsRadical x ↔ Squarefree x ∨ x = 0 :=
  ⟨fun hx ↦ (em <| x = 0).elim .inr fun h ↦ .inl <| hx.squarefree h,
    Or.rec Squarefree.isRadical <| by
      rintro rfl
      rw [zero_isRadical_iff]
      infer_instance⟩

-- DISSOLVED: isRadical_iff_squarefree_of_ne_zero

end IsRadical

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

-- DISSOLVED: _root_.exists_squarefree_dvd_pow_of_ne_zero

-- DISSOLVED: squarefree_iff_nodup_normalizedFactors

end UniqueFactorizationMonoid

namespace Int

@[simp]
theorem squarefree_natAbs {n : ℤ} : Squarefree n.natAbs ↔ Squarefree n := by
  simp_rw [Squarefree, natAbs_surjective.forall, ← natAbs_mul, natAbs_dvd_natAbs,
    isUnit_iff_natAbs_eq, Nat.isUnit_iff]

@[simp]
theorem squarefree_natCast {n : ℕ} : Squarefree (n : ℤ) ↔ Squarefree n := by
  rw [← squarefree_natAbs, natAbs_ofNat]

end Int
