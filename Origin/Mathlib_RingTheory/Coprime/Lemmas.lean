/-
Extracted from RingTheory/Coprime/Lemmas.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Additional lemmas about elements of a ring satisfying `IsCoprime`
and elements of a monoid satisfying `IsRelPrime`

These lemmas are in a separate file to the definition of `IsCoprime` or `IsRelPrime`
as they require more imports.

Notably, this includes lemmas about `Finset.prod` as this requires importing BigOperators, and
lemmas about `Pow` since these are easiest to prove via `Finset.prod`.

-/

universe u v

open scoped Function -- required for scoped `on` notation

section IsCoprime

variable {R : Type u} {I : Type v} [CommSemiring R] {x y z : R} {s : I → R} {t : Finset I}

theorem Int.isCoprime_iff_gcd_eq_one {m n : ℤ} : IsCoprime m n ↔ Int.gcd m n = 1 := by
  constructor
  · rintro ⟨a, b, h⟩
    refine Nat.dvd_one.mp (Int.gcd_dvd_iff.mpr ⟨a, b, ?_⟩)
    rwa [mul_comm m, mul_comm n, eq_comm]
  · rw [← Int.ofNat_inj, IsCoprime, Int.gcd_eq_gcd_ab, mul_comm m, mul_comm n, Nat.cast_one]
    intro h
    exact ⟨_, _, h⟩

-- INSTANCE (free from Core): :
