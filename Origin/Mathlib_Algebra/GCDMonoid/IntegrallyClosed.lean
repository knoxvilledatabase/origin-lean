/-
Extracted from Algebra/GCDMonoid/IntegrallyClosed.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# GCD domains are integrally closed

-/

open scoped Polynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem IsLocalization.surj_of_gcd_domain [GCDMonoid R] (M : Submonoid R) [IsLocalization M A]
    (z : A) : ∃ a b : R, IsUnit (gcd a b) ∧ z * algebraMap R A b = algebraMap R A a := by
  obtain ⟨x, ⟨y, hy⟩, rfl⟩ := IsLocalization.exists_mk'_eq M z
  obtain ⟨x', y', hx', hy', hu⟩ := extract_gcd x y
  use x', y', hu
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul]
  convert IsLocalization.mk'_mul_cancel_left (M := M) (S := A) _ _ using 2
  grind

-- INSTANCE (free from Core): (priority
