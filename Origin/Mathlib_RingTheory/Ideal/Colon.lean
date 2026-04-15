/-
Extracted from RingTheory/Ideal/Colon.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The colon ideal

This file defines `Submodule.colon N P` as the ideal of all elements `r : R` such that `r • P ⊆ N`.
The normal notation for this would be `N : P` which has already been taken by type theory.

-/

namespace Submodule

open Pointwise

variable {R M : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {N N₁ N₂ : Submodule R M} {S S₁ S₂ : Set M}

def colon (N : Submodule R M) (S : Set M) : Ideal R where
  carrier := {r : R | (r • S : Set M) ⊆ N}
  add_mem' ha hb :=
    (Set.add_smul_subset _ _ _).trans ((Set.add_subset_add ha hb).trans_eq (by simp))
  zero_mem' := (Set.zero_smul_set_subset S).trans (by simp)
  smul_mem' r := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, mul_smul, Set.smul_set_subset_iff]
    intro x hx y hy
    exact N.smul_mem _ (hx hy)

theorem mem_colon {r} : r ∈ N.colon S ↔ ∀ s ∈ S, r • s ∈ N := Set.smul_set_subset_iff
