/-
Extracted from RingTheory/Valuation/ValuationRing.lean
Genuine: 8 of 18 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Valuation Rings

A valuation ring is a domain such that for every pair of elements `a b`, either `a` divides
`b` or vice-versa.

Any valuation ring induces a natural valuation on its fraction field, as we show in this file.
Namely, given the following instances:
`[CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]`,
there is a natural valuation `Valuation A K` on `K` with values in `value_group A K` where
the image of `A` under `algebraMap A K` agrees with `(Valuation A K).integer`.

We also provide the equivalence of the following notions for a domain `R` in `ValuationRing.TFAE`.
1. `R` is a valuation ring.
2. For each `x : FractionRing K`, either `x` or `x⁻¹` is in `R`.
3. "divides" is a total relation on the elements of `R`.
4. "contains" is a total relation on the ideals of `R`.
5. `R` is a local bezout domain.

We also show that, given a valuation `v` on a field `K`, the ring of valuation integers is a
valuation ring and `K` is the fraction field of this ring.

## Implementation details

The Mathlib definition of a valuation ring requires `IsDomain A` even though the condition
does not mention zero divisors. Thus, there is a technical `PreValuationRing A` that
is defined in further generality that can be used in places where the ring cannot be a domain.
The `ValuationRing` class is kept to be in sync with the literature.

-/

assert_not_exists IsDiscreteValuationRing

universe u v w

class PreValuationRing (A : Type u) [Mul A] : Prop where
  cond' : ∀ a b : A, ∃ c : A, a * c = b ∨ b * c = a

lemma PreValuationRing.cond {A : Type u} [Mul A] [PreValuationRing A] (a b : A) :
    ∃ c : A, a * c = b ∨ b * c = a := @PreValuationRing.cond' A _ _ _ _

class ValuationRing (A : Type u) [CommRing A] [IsDomain A] : Prop extends PreValuationRing A

alias ValuationRing.cond := PreValuationRing.cond

namespace ValuationRing

variable (A : Type u) [CommRing A]

variable (K : Type v) [Field K] [Algebra A K]

def ValueGroup : Type v := Quotient (MulAction.orbitRel Aˣ K)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable [IsDomain A] [ValuationRing A] [IsFractionRing A K]

protected theorem le_total (a b : ValueGroup A K) : a ≤ b ∨ b ≤ a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  obtain ⟨xa, ya, hya, rfl⟩ := IsFractionRing.div_surjective A a
  obtain ⟨xb, yb, hyb, rfl⟩ := IsFractionRing.div_surjective A b
  have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
  have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
  obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
  · right
    use c
    rw [Algebra.smul_def]
    field_simp
    simp only [← map_mul]; congr 1; linear_combination h
  · left
    use c
    rw [Algebra.smul_def]
    field_simp
    simp only [← map_mul]; congr 1; linear_combination h

-- INSTANCE (free from Core): linearOrder

-- INSTANCE (free from Core): commGroupWithZero

-- INSTANCE (free from Core): linearOrderedCommGroupWithZero

noncomputable def valuation : Valuation K (ValueGroup A K) where
  toFun := Quotient.mk''
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add_le_max' := by
    intro a b
    obtain ⟨xa, ya, hya, rfl⟩ := IsFractionRing.div_surjective A a
    obtain ⟨xb, yb, hyb, rfl⟩ := IsFractionRing.div_surjective A b
    have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
    obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
    · apply le_trans _ (le_max_left _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [← map_mul, ← map_add]
      congr 1; linear_combination h
    · apply le_trans _ (le_max_right _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [← map_mul, ← map_add]
      congr 1; linear_combination h

theorem mem_integer_iff (x : K) : x ∈ (valuation A K).integer ↔ ∃ a : A, algebraMap A K a = x := by
  constructor
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def, mul_one]
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def, mul_one]

noncomputable def equivInteger : A ≃+* (valuation A K).integer :=
  RingEquiv.ofBijective
    (show A →ₙ+* (valuation A K).integer from
      { toFun := fun a => ⟨algebraMap A K a, (mem_integer_iff _ _ _).mpr ⟨a, rfl⟩⟩
        map_mul' := fun _ _ => by ext1; exact (algebraMap A K).map_mul _ _
        map_zero' := by ext1; exact (algebraMap A K).map_zero
        map_add' := fun _ _ => by ext1; exact (algebraMap A K).map_add _ _ })
    (by
      constructor
      · intro x y h
        apply_fun (algebraMap (valuation A K).integer K) at h
        exact IsFractionRing.injective _ _ h
      · rintro ⟨-, ha⟩
        rw [mem_integer_iff] at ha
        obtain ⟨a, rfl⟩ := ha
        exact ⟨a, rfl⟩)
