/-
Extracted from LinearAlgebra/Matrix/Stochastic.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Row- and Column-stochastic matrices

A square matrix `M` is *row-stochastic* if all its entries are non-negative and `M *ᵥ 1 = 1`.
Likewise, `M` is *column-stochastic* if all its entries are non-negative and `1 ᵥ* M = 1`. This
file defines these concepts and provides basic API for them.

Note that *doubly stochastic* matrices (i.e. matrices that are both row- and column-stochastic)
are defined in `Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean`.

## Main definitions

* `rowStochastic`: row-stochastic matrices indexed by `n` with entries in `R`, as a submonoid
  of `Matrix n n R`.
* `colStochastic R n`: column-stochastic matrices indexed by `n` with entries in `R`, as a
  submonoid of `Matrix n n R`.

-/

open Finset

namespace Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

def rowStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] : Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1  }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_⟩
    rw [← mulVec_mulVec, hN.2, hM.2]
  one_mem' := by
    simp [zero_le_one_elem]

lemma mem_rowStochastic_iff_sum :
    M ∈ rowStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) := by
  simp [funext_iff, rowStochastic, mulVec, dotProduct]

lemma nonneg_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) {i j : n} : 0 ≤ M i j :=
  hM.1 _ _

lemma sum_row_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) (i : n) : ∑ j, M i j = 1 :=
  (mem_rowStochastic_iff_sum.1 hM).2 _

lemma one_vecMul_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) : M *ᵥ 1 = 1 :=
  (mem_rowStochastic.1 hM).2

lemma le_one_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) {i j : n} :
    M i j ≤ 1 := by
  rw [← sum_row_of_mem_rowStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

lemma nonneg_vecMul_of_mem_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (x ᵥ* M) j := by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (hx k)
  exact nonneg_of_mem_rowStochastic hM

lemma nonneg_mulVec_of_mem_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (M *ᵥ x) j := by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_rowStochastic hM

lemma vecMul_dotProduct_one_eq_one_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : x ⬝ᵥ 1 = 1) : (x ᵥ* M) ⬝ᵥ 1 = 1 := by
  rw [← dotProduct_mulVec, hM.2, hx]

lemma convex_rowStochastic : Convex R (rowStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_rowStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]
