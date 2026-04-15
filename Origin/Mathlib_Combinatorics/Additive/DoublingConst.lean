/-
Extracted from Combinatorics/Additive/DoublingConst.lean
Genuine: 30 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Finset.Density

/-!
# Doubling and difference constants

This file defines the doubling and difference constants of two finsets in a group.
-/

open Finset

open scoped Pointwise

namespace Finset

section Group

variable {G G' : Type*} [Group G] [AddGroup G'] [DecidableEq G] [DecidableEq G'] {A B : Finset G}

@[to_additive
"The doubling constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A + B| / |A|`.
The notation `σ[A, B]` is available in scope `Combinatorics.Additive`."]
def mulConst (A B : Finset G) : ℚ≥0 := #(A * B) / #A

@[to_additive
"The difference constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A - B| / |A|`.
The notation `δ[A, B]` is available in scope `Combinatorics.Additive`."]
def divConst (A B : Finset G) : ℚ≥0 := #(A / B) / #A

scoped[Combinatorics.Additive] notation3:max "σₘ[" A ", " B "]" => Finset.mulConst A B

scoped[Combinatorics.Additive] notation3:max "σₘ[" A "]" => Finset.mulConst A A

scoped[Combinatorics.Additive] notation3:max "σ[" A ", " B "]" => Finset.addConst A B

scoped[Combinatorics.Additive] notation3:max "σ[" A "]" => Finset.addConst A A

scoped[Combinatorics.Additive] notation3:max "δₘ[" A ", " B "]" => Finset.divConst A B

scoped[Combinatorics.Additive] notation3:max "δₘ[" A "]" => Finset.divConst A A

scoped[Combinatorics.Additive] notation3:max "δ[" A ", " B "]" => Finset.subConst A B

scoped[Combinatorics.Additive] notation3:max "δ[" A "]" => Finset.subConst A A

open scoped Combinatorics.Additive

@[to_additive (attr := simp) addConst_mul_card]
lemma mulConst_mul_card (A B : Finset G) : σₘ[A, B] * #A = #(A * B) := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp) subConst_mul_card]
lemma divConst_mul_card (A B : Finset G) : δₘ[A, B] * #A = #(A / B) := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp) card_mul_addConst]
lemma card_mul_mulConst (A B : Finset G) : #A * σₘ[A, B] = #(A * B) := by
  rw [mul_comm, mulConst_mul_card]

@[to_additive (attr := simp) card_mul_subConst]
lemma card_mul_divConst (A B : Finset G) : #A * δₘ[A, B] = #(A / B) := by
  rw [mul_comm, divConst_mul_card]

@[to_additive (attr := simp)]
lemma mulConst_empty_left (B : Finset G) : σₘ[∅, B] = 0 := by simp [mulConst]

@[to_additive (attr := simp)]
lemma divConst_empty_left (B : Finset G) : δₘ[∅, B] = 0 := by simp [divConst]

@[to_additive (attr := simp)]
lemma mulConst_empty_right (A : Finset G) : σₘ[A, ∅] = 0 := by simp [mulConst]

@[to_additive (attr := simp)]
lemma divConst_empty_right (A : Finset G) : δₘ[A, ∅] = 0 := by simp [divConst]

@[to_additive (attr := simp)]
lemma mulConst_inv_right (A B : Finset G) : σₘ[A, B⁻¹] = δₘ[A, B] := by
  rw [mulConst, divConst, ← div_eq_mul_inv]

@[to_additive (attr := simp)]
lemma divConst_inv_right (A B : Finset G) : δₘ[A, B⁻¹] = σₘ[A, B] := by
  rw [mulConst, divConst, div_inv_eq_mul]

section Fintype

variable [Fintype G]

@[to_additive addConst_le_inv_dens "Dense sets have small doubling."]
lemma mulConst_le_inv_dens : σₘ[A, B] ≤ A.dens⁻¹ := by
  rw [dens, inv_div, mulConst]; gcongr; exact card_le_univ _

@[to_additive subConst_le_inv_dens "Dense sets have small difference constant."]
lemma divConst_le_inv_dens : δₘ[A, B] ≤ A.dens⁻¹ := by
  rw [dens, inv_div, divConst]; gcongr; exact card_le_univ _

end Fintype

variable {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]

lemma cast_addConst (A B : Finset G') : (σ[A, B] : 𝕜) = #(A + B) / #A := by
  simp [addConst]

lemma cast_subConst (A B : Finset G') : (δ[A, B] : 𝕜) = #(A - B) / #A := by
  simp [subConst]

@[to_additive existing]
lemma cast_mulConst (A B : Finset G) : (σₘ[A, B] : 𝕜) = #(A * B) / #A := by simp [mulConst]

@[to_additive existing]
lemma cast_divConst (A B : Finset G) : (δₘ[A, B] : 𝕜) = #(A / B) / #A := by simp [divConst]

lemma cast_addConst_mul_card (A B : Finset G') : (σ[A, B] * #A : 𝕜) = #(A + B) := by
  norm_cast; exact addConst_mul_card _ _

lemma cast_subConst_mul_card (A B : Finset G') : (δ[A, B] * #A : 𝕜) = #(A - B) := by
  norm_cast; exact subConst_mul_card _ _

lemma card_mul_cast_addConst (A B : Finset G') : (#A * σ[A, B] : 𝕜) = #(A + B) := by
  norm_cast; exact card_mul_addConst _ _

lemma card_mul_cast_subConst (A B : Finset G') : (#A * δ[A, B] : 𝕜) = #(A - B) := by
  norm_cast; exact card_mul_subConst _ _

@[to_additive (attr := simp) existing cast_addConst_mul_card]
lemma cast_mulConst_mul_card (A B : Finset G) : (σₘ[A, B] * #A : 𝕜) = #(A * B) := by
  norm_cast; exact mulConst_mul_card _ _

@[to_additive (attr := simp) existing cast_subConst_mul_card]
lemma cast_divConst_mul_card (A B : Finset G) : (δₘ[A, B] * #A : 𝕜) = #(A / B) := by
  norm_cast; exact divConst_mul_card _ _

@[to_additive (attr := simp) existing card_mul_cast_addConst]
lemma card_mul_cast_mulConst (A B : Finset G) : (#A * σₘ[A, B] : 𝕜) = #(A * B) := by
  norm_cast; exact card_mul_mulConst _ _

@[to_additive (attr := simp) existing card_mul_cast_subConst]
lemma card_mul_cast_divConst (A B : Finset G) : (#A * δₘ[A, B] : 𝕜) = #(A / B) := by
  norm_cast; exact card_mul_divConst _ _

end Group

open scoped Combinatorics.Additive

section CommGroup

variable {G : Type*} [CommGroup G] [DecidableEq G] {A B : Finset G}

@[to_additive (attr := simp)]
lemma mulConst_inv_left (A B : Finset G) : σₘ[A⁻¹, B] = δₘ[A, B] := by
  rw [mulConst, divConst, card_inv, ← card_inv, mul_inv_rev, inv_inv, inv_mul_eq_div]

@[to_additive (attr := simp)]
lemma divConst_inv_left (A B : Finset G) : δₘ[A⁻¹, B] = σₘ[A, B] := by
  rw [mulConst, divConst, card_inv, ← card_inv, inv_div, div_inv_eq_mul, mul_comm]

@[to_additive
"If `A` has small difference, then it has small doubling, with the constant squared.
This is a consequence of the Ruzsa triangle inequality."]
lemma mulConst_le_divConst_sq : σₘ[A] ≤ δₘ[A] ^ 2 := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < #A * #A)
  calc
    _ = #(A * A) * (#A : ℚ≥0) := by rw [← mul_assoc, mulConst_mul_card]
    _ ≤ #(A / A) * #(A / A) := by norm_cast; exact ruzsa_triangle_inequality_mul_div_div ..
    _ = _ := by rw [← divConst_mul_card]; ring

@[to_additive
"If `A` has small doubling, then it has small difference, with the constant squared.
This is a consequence of the Ruzsa triangle inequality."]
lemma divConst_le_mulConst_sq : δₘ[A] ≤ σₘ[A] ^ 2 := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < #A * #A)
  calc
    _ = #(A / A) * (#A : ℚ≥0) := by rw [← mul_assoc, divConst_mul_card]
    _ ≤ #(A * A) * #(A * A) := by norm_cast; exact ruzsa_triangle_inequality_div_mul_mul ..
    _ = _ := by rw [← mulConst_mul_card]; ring

end CommGroup

end Finset
