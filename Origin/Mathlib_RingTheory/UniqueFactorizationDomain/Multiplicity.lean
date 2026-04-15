/-
Extracted from RingTheory/UniqueFactorizationDomain/Multiplicity.lean
Genuine: 2 | Conflates: 0 | Dissolved: 6 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Unique factorization and multiplicity

## Main results

* `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`: The multiplicity of an
  irreducible factor of a nonzero element is exactly the number of times the normalized factor
  occurs in the `normalizedFactors`.
-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

-- DISSOLVED: WfDvdMonoid.max_power_factor'

-- DISSOLVED: WfDvdMonoid.max_power_factor

-- DISSOLVED: multiplicity.finite_of_not_isUnit

namespace UniqueFactorizationMonoid

variable {R : Type*} [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

section multiplicity

variable [NormalizationMonoid R]

open Multiset

section

-- DISSOLVED: le_emultiplicity_iff_replicate_le_normalizedFactors

-- DISSOLVED: emultiplicity_eq_count_normalizedFactors

end

theorem count_normalizedFactors_eq [DecidableEq R] {p x : R} (hp : Irreducible p)
    (hnorm : normalize p = p) {n : ℕ} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by classical
  by_cases hx0 : x = 0
  · simp [hx0] at hlt
  apply Nat.cast_injective (R := ℕ∞)
  convert (emultiplicity_eq_count_normalizedFactors hp hx0).symm
  · exact hnorm.symm
  exact (emultiplicity_eq_coe.mpr ⟨hle, hlt⟩).symm

theorem count_normalizedFactors_eq' [DecidableEq R] {p x : R} (hp : p = 0 ∨ Irreducible p)
    (hnorm : normalize p = p) {n : ℕ} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  rcases hp with (rfl | hp)
  · cases n
    · exact count_eq_zero.2 (zero_not_mem_normalizedFactors _)
    · rw [zero_pow (Nat.succ_ne_zero _)] at hle hlt
      exact absurd hle hlt
  · exact count_normalizedFactors_eq hp hnorm hle hlt

end multiplicity

-- DISSOLVED: max_power_factor

end UniqueFactorizationMonoid
