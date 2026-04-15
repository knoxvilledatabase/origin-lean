/-
Extracted from NumberTheory/NumberField/House.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# House of an algebraic number
This file defines the house of an algebraic number `α`, which is
the largest of the modulus of its conjugates.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [Hua, L.-K., *Introduction to number theory*][hua1982house]

## Tags
number field, algebraic number, house
-/

variable {K : Type*} [Field K] [NumberField K]

namespace NumberField

noncomputable section

open Module.Free Module canonicalEmbedding Matrix Finset

attribute [local instance] Matrix.seminormedAddCommGroup

def house (α : K) : ℝ := ‖canonicalEmbedding K α‖

theorem house_eq_sup' (α : K) :
    house α = univ.sup' univ_nonempty (fun φ : K →+* ℂ ↦ ‖φ α‖₊) := by
  rw [house, ← coe_nnnorm, nnnorm_eq, ← sup'_eq_sup univ_nonempty]

theorem house_sum_le_sum_house {ι : Type*} (s : Finset ι) (α : ι → K) :
    house (∑ i ∈ s, α i) ≤ ∑ i ∈ s, house (α i) := by
  simp only [house, map_sum]; apply norm_sum_le_of_le; intros; rfl

theorem house_nonneg (α : K) : 0 ≤ house α := norm_nonneg _

theorem house_mul_le (α β : K) : house (α * β) ≤ house α * house β := by
  simp only [house, map_mul]; apply norm_mul_le

lemma house_prod_le (s : Finset K) : house (∏ x ∈ s, x) ≤ ∏ x ∈ s, house x := by
  simpa [house, map_prod] using Finset.norm_prod_le _ _

theorem house_add_le (α β : K) : house (α + β) ≤ house α + house β := by
  simp only [house, map_add]; apply norm_add_le

theorem house_pow_le (α : K) (i : ℕ) : house (α ^ i) ≤ house α ^ i := by
  simpa only [house, map_pow] using norm_pow_le ((canonicalEmbedding K) α) i

theorem house_nat_mul (α : K) (c : ℕ) : house (c * α) = c * house α := by
  rw [house_eq_sup', house_eq_sup', Finset.sup'_eq_sup, Finset.sup'_eq_sup]
  norm_cast
  simp [NNReal.mul_finset_sup]
