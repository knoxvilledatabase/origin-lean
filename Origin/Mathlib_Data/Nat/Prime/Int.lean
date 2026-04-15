/-
Extracted from Data/Nat/Prime/Int.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Prime numbers in the naturals and the integers

TODO: This file can probably be merged with `Mathlib/Data/Int/NatPrime.lean`.
-/

namespace Nat

theorem prime_iff_prime_int {p : ℕ} : p.Prime ↔ _root_.Prime (p : ℤ) :=
  ⟨fun hp =>
    ⟨Int.natCast_ne_zero_iff_pos.2 hp.pos, mt Int.isUnit_iff_natAbs_eq.1 hp.ne_one, fun a b h => by
      rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast, Int.natAbs_mul, hp.dvd_mul] at h
      rwa [← Int.dvd_natAbs, Int.natCast_dvd_natCast, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]⟩,
    fun hp =>
    Nat.prime_iff.2
      ⟨Int.natCast_ne_zero.1 hp.1,
        (mt Nat.isUnit_iff.1) fun h => by simp [h] at hp, fun a b => by
        simpa only [Int.natCast_dvd_natCast, (Int.natCast_mul _ _).symm] using hp.2.2 a b⟩⟩

lemma Prime.pow_inj {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ^ (m + 1) = q ^ (n + 1)) : p = q ∧ m = n := by
  have H := dvd_antisymm (Prime.dvd_of_dvd_pow hp <| h ▸ dvd_pow_self p (succ_ne_zero m))
    (Prime.dvd_of_dvd_pow hq <| h.symm ▸ dvd_pow_self q (succ_ne_zero n))
  exact ⟨H, succ_inj.mp <| Nat.pow_right_injective hq.two_le (H ▸ h)⟩

-- DISSOLVED: Prime.pow_inj'

end Nat

namespace Int
