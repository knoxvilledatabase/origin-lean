/-
Extracted from Algebra/Order/CauSeq/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cauchy sequences

A basic theory of Cauchy sequences, used in the construction of the reals and p-adic numbers. Where
applicable, lemmas that will be reused in other contexts have been stated in extra generality.
There are other "versions" of Cauchyness in the library, in particular Cauchy filters in topology.
This is a concrete implementation that is useful for simplicity and computability reasons.

## Important definitions

* `IsCauSeq`: a predicate that says `f : ℕ → β` is Cauchy.
* `CauSeq`: the type of Cauchy sequences valued in type `β` with respect to an absolute value
  function `abv`.

## Tags

sequence, cauchy, abs val, absolute value
-/

assert_not_exists Finset Module Submonoid FloorRing

variable {α β : Type*}

open IsAbsoluteValue

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  (abv : β → α) [IsAbsoluteValue abv]

theorem rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ →
      abv (a₁ + a₂ - (b₁ + b₂)) < ε :=
  ⟨ε / 2, half_pos ε0, fun {a₁ a₂ b₁ b₂} h₁ h₂ => by
    simpa [add_halves, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      lt_of_le_of_lt (abv_add abv _ _) (add_lt_add h₁ h₂)⟩

theorem rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ → abv b₂ < K₂ → abv (a₁ - b₁) < δ →
      abv (a₂ - b₂) < δ → abv (a₁ * a₂ - b₁ * b₂) < ε := by
  have K0 : (0 : α) < max 1 (max K₁ K₂) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have εK := div_pos (half_pos ε0) K0
  refine ⟨_, εK, fun {a₁ a₂ b₁ b₂} ha₁ hb₂ h₁ h₂ => ?_⟩
  replace ha₁ := lt_of_lt_of_le ha₁ (le_trans (le_max_left _ K₂) (le_max_right 1 _))
  replace hb₂ := lt_of_lt_of_le hb₂ (le_trans (le_max_right K₁ _) (le_max_right 1 _))
  set M := max 1 (max K₁ K₂)
  have : abv (a₁ - b₁) * abv b₂ + abv (a₂ - b₂) * abv a₁ < ε / 2 / M * M + ε / 2 / M * M := by
    gcongr
  rw [← abv_mul abv, mul_comm, div_mul_cancel₀ _ (ne_of_gt K0), ← abv_mul abv, add_halves] at this
  simpa [sub_eq_add_neg, mul_add, add_mul, add_left_comm] using
    lt_of_le_of_lt (abv_add abv _ _) this

theorem rat_inv_continuous_lemma {β : Type*} [DivisionRing β] (abv : β → α) [IsAbsoluteValue abv]
    {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K) :
    ∃ δ > 0, ∀ {a b : β}, K ≤ abv a → K ≤ abv b → abv (a - b) < δ → abv (a⁻¹ - b⁻¹) < ε := by
  refine ⟨K * ε * K, mul_pos (mul_pos K0 ε0) K0, fun {a b} ha hb h => ?_⟩
  have a0 := K0.trans_le ha
  have b0 := K0.trans_le hb
  rw [inv_sub_inv' ((abv_pos abv).1 a0) ((abv_pos abv).1 b0), abv_mul abv, abv_mul abv, abv_inv abv,
    abv_inv abv, abv_sub abv]
  refine lt_of_mul_lt_mul_left (lt_of_mul_lt_mul_right ?_ b0.le) a0.le
  rw [mul_assoc, inv_mul_cancel_right₀ b0.ne', ← mul_assoc, mul_inv_cancel₀ a0.ne', one_mul]
  refine h.trans_le ?_
  gcongr
  exact mul_nonneg a0.le ε0.le

end
