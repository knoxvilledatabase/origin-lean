/-
Extracted from RingTheory/Localization/NumDen.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Numerator and denominator in a localization

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

namespace IsFractionRing

open IsLocalization

section NumDen

variable (A : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

theorem exists_reduced_fraction (x : K) :
    ∃ (a : A) (b : nonZeroDivisors A), IsRelPrime a b ∧ mk' K a b = x := by
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (nonZeroDivisors A) x
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b
      (mem_nonZeroDivisors_iff_ne_zero.mp b_nonzero)
  obtain ⟨_, b'_nonzero⟩ := mul_mem_nonZeroDivisors.mp b_nonzero
  refine ⟨a', ⟨b', b'_nonzero⟩, no_factor, ?_⟩
  refine mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b_nonzero) ?_
  simp only [map_mul, Algebra.smul_def] at *
  rw [← hab, mul_assoc, mk'_spec' _ a' ⟨b', b'_nonzero⟩]

noncomputable def num (x : K) : A :=
  Classical.choose (exists_reduced_fraction A x)

noncomputable def den (x : K) : nonZeroDivisors A :=
  Classical.choose (Classical.choose_spec (exists_reduced_fraction A x))

theorem num_den_reduced (x : K) : IsRelPrime (num A x) (den A x) :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).1

theorem mk'_num_den (x : K) : mk' K (num A x) (den A x) = x :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).2
