/-
Extracted from Analysis/Convex/DoublyStochasticMatrix.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Doubly stochastic matrices

## Main definitions

* `doublyStochastic`: a square matrix is doubly stochastic if all entries are nonnegative, and left
  or right multiplication by the vector of all 1s gives the vector of all 1s. Equivalently, all
  row and column sums are equal to 1.

## Main statements

* `convex_doublyStochastic`: The set of doubly stochastic matrices is convex.
* `permMatrix_mem_doublyStochastic`: Any permutation matrix is doubly stochastic.

## Tags

Doubly stochastic, Birkhoff's theorem, Birkhoff-von Neumann theorem
-/

open Finset Function Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

def doublyStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] :
    Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_, ?_⟩
    next => rw [← mulVec_mulVec, hN.2.1, hM.2.1]
    next => rw [← vecMul_vecMul, hM.2.2, hN.2.2]
  one_mem' := by simp [zero_le_one_elem]

lemma mem_doublyStochastic_iff_sum :
    M ∈ doublyStochastic R n ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧ ∀ j, ∑ i, M i j = 1 := by
  simp [funext_iff, doublyStochastic, mulVec, vecMul, dotProduct]
