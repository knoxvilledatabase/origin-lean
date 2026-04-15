/-
Extracted from Algebra/Prime/Defs.lean
Genuine: 8 of 11 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Prime elements

In this file we define the predicate `Prime p`
saying that an element of a commutative monoid with zero is prime.
Namely, `Prime p` means that `p` isn't zero, it isn't a unit,
and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`;

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Irreducible`
(see `irreducible_iff_prime`), however this is not true in general.

## Main definitions

* `Prime`: a prime element of a commutative monoid with zero

## Main results

* `irreducible_iff_prime`: the two definitions are equivalent in a decomposition monoid.
-/

assert_not_exists IsOrderedMonoid Multiset

variable {M : Type*}

section Prime

variable [CommMonoidWithZero M]

def Prime (p : M) : Prop :=
  p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b

namespace Prime

variable {p : M} (hp : Prime p)

include hp

-- DISSOLVED: ne_zero

theorem not_unit : ¬IsUnit p :=
  hp.2.1

theorem not_dvd_one : ¬p ∣ 1 :=
  mt (isUnit_of_dvd_one ·) hp.not_unit

-- DISSOLVED: ne_one

theorem dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  hp.2.2 a b h

theorem dvd_mul {a b : M} : p ∣ a * b ↔ p ∣ a ∨ p ∣ b :=
  ⟨hp.dvd_or_dvd, (Or.elim · (dvd_mul_of_dvd_left · _) (dvd_mul_of_dvd_right · _))⟩

theorem isPrimal : IsPrimal p := fun _a _b dvd ↦ (hp.dvd_or_dvd dvd).elim
  (fun h ↦ ⟨p, 1, h, one_dvd _, (mul_one p).symm⟩) fun h ↦ ⟨1, p, one_dvd _, h, (one_mul p).symm⟩

theorem not_dvd_mul {a b : M} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b :=
  hp.dvd_mul.not.mpr <| not_or.mpr ⟨ha, hb⟩

theorem dvd_of_dvd_pow {a : M} {n : ℕ} (h : p ∣ a ^ n) : p ∣ a := by
  induction n with
  | zero =>
    rw [pow_zero] at h
    have := isUnit_of_dvd_one h
    have := not_unit hp
    contradiction
  | succ n ih =>
    rw [pow_succ'] at h
    rcases dvd_or_dvd hp h with dvd_a | dvd_pow
    · assumption
    · exact ih dvd_pow

-- DISSOLVED: dvd_pow_iff_dvd

end Prime
