/-
Extracted from GroupTheory/Perm/Cycle/Type.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Cycle Types

In this file we define the cycle type of a permutation.

## Main definitions

- `Equiv.Perm.cycleType σ` where `σ` is a permutation of a `Fintype`
- `Equiv.Perm.partition σ` where `σ` is a permutation of a `Fintype`

## Main results

- `sum_cycleType` : The sum of `σ.cycleType` equals `σ.support.card`
- `lcm_cycleType` : The lcm of `σ.cycleType` equals `orderOf σ`
- `isConj_iff_cycleType_eq` : Two permutations are conjugate if and only if they have the same
  cycle type.
- `exists_prime_orderOf_dvd_card`: For every prime `p` dividing the order of a finite group `G`
  there exists an element of order `p` in `G`. This is known as Cauchy's theorem.
-/

open scoped Finset

namespace Equiv.Perm

open List (Vector)

open Equiv List Multiset

variable {α : Type*} [Fintype α]

section CycleType

variable [DecidableEq α]

def cycleType (σ : Perm α) : Multiset ℕ :=
  σ.cycleFactorsFinset.1.map (Finset.card ∘ support)

theorem cycleType_eq' {σ : Perm α} (s : Finset (Perm α)) (h1 : ∀ f : Perm α, f ∈ s → f.IsCycle)
    (h2 : (s : Set (Perm α)).Pairwise Disjoint)
    (h0 : s.noncommProd id (h2.imp fun _ _ => Disjoint.commute) = σ) :
    σ.cycleType = s.1.map (Finset.card ∘ support) := by
  rw [cycleType_def]
  congr
  rw [cycleFactorsFinset_eq_finset]
  exact ⟨h1, h2, h0⟩

theorem cycleType_eq {σ : Perm α} (l : List (Perm α)) (h0 : l.prod = σ)
    (h1 : ∀ σ : Perm α, σ ∈ l → σ.IsCycle) (h2 : l.Pairwise Disjoint) :
    σ.cycleType = l.map (Finset.card ∘ support) := by
  have hl : l.Nodup := nodup_of_pairwise_disjoint_cycles h1 h2
  rw [cycleType_eq' l.toFinset]
  · simp [List.dedup_eq_self.mpr hl, Function.comp_def]
  · simpa using h1
  · simpa [hl] using h2
  · simp [hl, h0]

theorem CycleType.count_def {σ : Perm α} (n : ℕ) :
    σ.cycleType.count n =
      Fintype.card {c : σ.cycleFactorsFinset // #(c : Perm α).support = n } := by
  -- work on the LHS
  rw [cycleType, Multiset.count_eq_card_filter_eq]
  -- rewrite the `Fintype.card` as a `Finset.card`
  rw [Fintype.subtype_card, Finset.univ_eq_attach, Finset.filter_attach',
    Finset.card_map, Finset.card_attach]
  simp only [Function.comp_apply, Finset.card, Finset.filter_val,
    Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro d h
  simp only [eq_comm, Finset.mem_val.mp h, exists_const]
