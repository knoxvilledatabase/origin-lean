/-
Extracted from LinearAlgebra/Matrix/DotProduct.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dot product of two vectors

This file contains some results on the map `dotProduct`, which maps two
vectors `v w : n → R` to the sum of the entrywise products `v i * w i`.

## Main results

* `dotProduct_stdBasis_one`: the dot product of `v` with the `i`th
  standard basis vector is `v i`
* `dotProduct_eq_zero_iff`: if `v`'s dot product with all `w` is zero,
  then `v` is zero

## Tags

matrix

-/

variable {m n p R : Type*}

section Semiring

variable [Semiring R] [Fintype n]

theorem dotProduct_eq (v w : n → R) (h : ∀ u, v ⬝ᵥ u = w ⬝ᵥ u) : v = w := by
  funext x
  classical rw [← dotProduct_single_one v x, ← dotProduct_single_one w x, h]

theorem dotProduct_eq_iff {v w : n → R} : (∀ u, v ⬝ᵥ u = w ⬝ᵥ u) ↔ v = w :=
  ⟨fun h => dotProduct_eq v w h, fun h _ => h ▸ rfl⟩

theorem dotProduct_eq_zero (v : n → R) (h : ∀ w, v ⬝ᵥ w = 0) : v = 0 :=
  dotProduct_eq _ _ fun u => (h u).symm ▸ (zero_dotProduct u).symm

theorem dotProduct_eq_zero_iff {v : n → R} : (∀ w, v ⬝ᵥ w = 0) ↔ v = 0 :=
  ⟨fun h => dotProduct_eq_zero v h, fun h w => h.symm ▸ zero_dotProduct w⟩

end Semiring

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Fintype n]

lemma dotProduct_nonneg_of_nonneg {v w : n → R} (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ v ⬝ᵥ w :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hw i))

lemma dotProduct_le_dotProduct_of_nonneg_right {u v w : n → R} (huv : u ≤ v) (hw : 0 ≤ w) :
    u ⬝ᵥ w ≤ v ⬝ᵥ w := by
  unfold dotProduct; gcongr <;> apply_rules

lemma dotProduct_le_dotProduct_of_nonneg_left {u v w : n → R} (huv : u ≤ v) (hw : 0 ≤ w) :
    w ⬝ᵥ u ≤ w ⬝ᵥ v := by
  unfold dotProduct; gcongr <;> apply_rules

end OrderedSemiring

section Self

variable [Fintype m] [Fintype n] [Fintype p]
